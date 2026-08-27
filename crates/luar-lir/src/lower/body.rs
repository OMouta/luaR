//! Lowering one function body.
//!
//! Values are in SSA, built as the body is walked. A binding is a name for
//! whatever value it currently holds, and assigning to it names another; the
//! block parameters that merge two of those come in with the control flow
//! that needs them.
//!
//! Every expression is emitted in the order it is written (LR55). An operand
//! is lowered before the instruction that reads it, and where one expression
//! holds two, the left is emitted first. That is not an optimization choice
//! left for later: it is the order, and it is written down here once.

use std::collections::HashMap;

use luar_ast::{
    Argument, ArmBody, BinaryOp as AstBinary, Binding, Block, Branch, Expr, ExprKind, FieldInit,
    FieldPattern, MapEntry, MapKey, MatchArm, Pattern, PatternKind, Payload, Stmt, StmtKind,
    UnaryOp as AstUnary,
};
use luar_diagnostics::Span;
use luar_sema::facts::Facts;

use luar_sema::types::Type;

use crate::inst::MethodId;
use crate::inst::{BinaryOp, Const, Inst, InstKind, Target, Terminator, Trap, UnaryOp, Value};
use crate::lower::types::{self, Ids};
use crate::lower::{Callee, Gap};
use crate::program::{BlockId, Function, Program, Shape};
use crate::ty::{Builtin, IntTy, Ty, TypeId};

/// A binding, told apart from every other one with its name (LR53).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct Var(u32);

/// One path reaching the end of a construct: the block it left from, and what
/// every binding held there.
struct Arrival {
    block: BlockId,
    defs: HashMap<Var, Value>,
}

/// A loop being lowered, and where leaving it goes (LR10.6, LR10.7).
struct Loop {
    label: Option<String>,
    /// Where `continue` goes. Absent for a `repeat`, whose condition is part
    /// of its body and so has no block of its own (LR10.3).
    again: Option<BlockId>,
    /// Where `break` goes.
    exit: BlockId,
    /// The bindings both of those pass along.
    carried: Vec<Var>,
    /// How many scopes were open around the loop, so that leaving it runs
    /// what every scope inside it deferred (LR26).
    depth: usize,
}

#[derive(Debug, Clone, Copy)]
enum Exit {
    Break,
    Continue,
}

/// What lowering a body needs from the rest of the program.
pub(super) struct Context<'a> {
    pub facts: &'a Facts,
    pub ids: &'a Ids,
    /// What each function declaration became, by the span the checker
    /// recorded a call as reaching (LR40, LR76).
    pub callees: &'a HashMap<Span, Callee>,
    /// The interface methods, which have declarations and no bodies (LR18.1).
    pub virtuals: &'a HashMap<Span, MethodId>,
    /// The default written beside a field (LR12.2).
    pub defaults: &'a HashMap<(TypeId, u32), Expr>,
    pub program: &'a Program,
}

pub(super) struct Body<'a> {
    context: Context<'a>,
    function: Function,
    /// The block instructions are being appended to.
    current: BlockId,
    /// Whether that block has already been left, which is what makes the
    /// statements after a `return` unreachable (LR50).
    left: bool,
    /// The names in scope, innermost last. A name written twice in one scope
    /// shadows rather than replaces, so each scope is a list (LR53).
    scopes: Vec<Vec<(String, Var)>>,
    /// What each open scope has deferred, in the order it was written
    /// (LR26). One frame per entry in `scopes`.
    deferred: Vec<Vec<Expr>>,
    /// The value each binding currently holds.
    defs: HashMap<Var, Value>,
    next_var: u32,
    /// The loops open around what is being lowered, innermost last.
    loops: Vec<Loop>,
    gaps: Vec<Gap>,
}

impl<'a> Body<'a> {
    pub(super) fn new(context: Context<'a>, mut function: Function) -> Self {
        let entry = function.entry;
        // The shell says it never returns, which is what an unlowered
        // function is. Lowering a body replaces that.
        function.block_mut(entry).term = None;
        Self {
            context,
            function,
            current: entry,
            left: false,
            scopes: vec![Vec::new()],
            deferred: vec![Vec::new()],
            defs: HashMap::new(),
            next_var: 0,
            loops: Vec::new(),
            gaps: Vec::new(),
        }
    }

    /// Binds `names` to the entry block's parameters, in order, and lowers
    /// `block` into the function.
    pub(super) fn lower(mut self, names: &[String], block: &Block) -> (Function, Vec<Gap>) {
        let params: Vec<Value> = self.function.block(self.function.entry).params.clone();
        for (name, value) in names.iter().zip(params) {
            let var = self.declare(name);
            self.defs.insert(var, value);
        }

        self.block(block);

        // LR9.1: a body that runs off its end returns nothing, which is only
        // a value where the function writes no result. Falling off one that
        // does is the checker's to report, and control cannot be here.
        if !self.left {
            let span = block.span;
            let term = if self.function.result == Ty::Unit {
                let unit = self.emit(InstKind::Const(Const::Unit), Ty::Unit, span);
                Terminator::Return(unit)
            } else {
                Terminator::Trap(Trap::Unreachable)
            };
            self.terminate(term);
        }

        (self.function, self.gaps)
    }

    // -- building ---------------------------------------------------------

    fn emit(&mut self, kind: InstKind, ty: Ty, span: Span) -> Value {
        let result = self.function.add_value(ty);
        self.function.block_mut(self.current).insts.push(Inst {
            result: Some(result),
            kind,
            span,
        });
        result
    }

    fn terminate(&mut self, term: Terminator) {
        let block = self.function.block_mut(self.current);
        if block.term.is_none() {
            block.term = Some(term);
        }
        self.left = true;
    }

    fn gap(&mut self, span: Span, what: impl Into<String>) {
        self.gaps.push(Gap {
            span,
            what: what.into(),
        });
    }

    /// A value standing in for one lowering could not build. It keeps the
    /// function well formed; the gap beside it says the program did not
    /// lower.
    fn missing(&mut self, span: Span, what: impl Into<String>) -> Value {
        self.gap(span, what);
        self.emit(InstKind::Const(Const::Unit), Ty::Never, span)
    }

    // -- scopes -----------------------------------------------------------

    fn declare(&mut self, name: &str) -> Var {
        let var = Var(self.next_var);
        self.next_var += 1;
        self.scopes
            .last_mut()
            .expect("a scope is open")
            .push((name.to_owned(), var));
        var
    }

    /// Opens a scope. Bindings and deferred expressions belong to the
    /// innermost one.
    fn open(&mut self) {
        self.scopes.push(Vec::new());
        self.deferred.push(Vec::new());
    }

    /// Closes the innermost scope, running what it deferred where control
    /// reaches its end (LR26).
    fn close(&mut self) {
        if !self.left {
            self.unwind(self.scopes.len() - 1);
        }
        self.scopes.pop();
        self.deferred.pop();
    }

    /// Runs what scope `frame` deferred, in reverse order of registration
    /// (LR26).
    fn unwind(&mut self, frame: usize) {
        for deferred in self.deferred[frame].clone().iter().rev() {
            self.expr(deferred, None);
        }
    }

    /// Runs what every scope from `depth` outward deferred, innermost first,
    /// which is what leaving several of them at once does (LR26).
    fn unwind_from(&mut self, depth: usize) {
        for frame in (depth..self.scopes.len()).rev() {
            self.unwind(frame);
        }
    }

    fn lookup(&self, name: &str) -> Option<Var> {
        self.scopes.iter().rev().find_map(|scope| {
            scope
                .iter()
                .rev()
                .find(|(bound, _)| bound == name)
                .map(|(_, var)| *var)
        })
    }

    // -- types ------------------------------------------------------------

    /// What the checker gave the expression at `span`, as an LIR type.
    fn recorded(&mut self, span: Span) -> Ty {
        let Some(ty) = self.context.facts.type_of(span).cloned() else {
            return self.missing_type(span, "an expression the checker did not type");
        };
        match types::convert(&ty, self.context.ids) {
            Ok(converted) => converted,
            Err(refused) => self.missing_type(span, refused),
        }
    }

    /// The same, without recording a gap where there is none, for a caller
    /// that has another way to work the type out.
    fn maybe_recorded(&self, span: Span) -> Option<Ty> {
        let ty = self.context.facts.type_of(span)?;
        types::convert(ty, self.context.ids).ok()
    }

    /// A value the checker proved holds something, ready to be read through.
    ///
    /// LR57: narrowing is what makes `user.id` legal after `user ~= nil`. The
    /// checker did that proof; the value is still an optional here, and this
    /// is where it stops being one.
    fn settled(&mut self, value: Value, span: Span) -> Value {
        let held = self.function.type_of(value).clone();
        match held {
            Ty::Optional(inner) => self.emit(InstKind::Unwrap { value }, *inner, span),
            _ => value,
        }
    }

    fn missing_type(&mut self, span: Span, what: impl Into<String>) -> Ty {
        self.gap(span, what);
        Ty::Never
    }

    /// The type an expression definitely has, where it has one.
    ///
    /// A binding is read from the value it holds, which is what lowering
    /// already worked out and is never less than what the checker knows: a
    /// name a pattern bound is unresolved to the checker and has a type here
    /// (LR16.2, LR57). A literal has no type of its own until context asks
    /// for one (LR39).
    fn known_type(&mut self, expr: &Expr) -> Option<Ty> {
        if let ExprKind::Name(name) = &expr.kind
            && let Some(var) = self.lookup(name)
            && let Some(value) = self.defs.get(&var)
        {
            return Some(self.function.type_of(*value).clone());
        }

        let held = self.context.facts.type_of(expr.span)?;
        if matches!(
            held,
            Type::IntegerLiteral(_)
                | Type::FloatLiteral
                | Type::SequenceLiteral(_)
                | Type::Unresolved
        ) {
            return None;
        }
        types::convert(held, self.context.ids).ok()
    }

    /// The type both operands of an operator are read at.
    ///
    /// A literal takes its type from the other operand where the other one
    /// has one, which is the same rule the checker applied (LR39).
    fn operand_type(&mut self, left: &Expr, right: &Expr) -> Ty {
        if let Some(ty) = self.known_type(left) {
            return ty;
        }
        if let Some(ty) = self.known_type(right) {
            return ty;
        }
        self.recorded(left.span)
    }

    // -- statements -------------------------------------------------------

    fn block(&mut self, block: &Block) {
        self.open();
        for stmt in &block.stmts {
            if self.left {
                // LR50: nothing after a block was left runs, so nothing after
                // it is lowered.
                break;
            }
            self.stmt(stmt);
        }
        self.close();
    }

    fn stmt(&mut self, stmt: &Stmt) {
        match &stmt.kind {
            StmtKind::Local { binding, ty, value } => {
                self.local(binding, ty.as_ref(), value.as_ref(), stmt.span)
            }
            StmtKind::Const {
                binding, ty, value, ..
            } => self.local(binding, ty.as_ref(), Some(value), stmt.span),
            StmtKind::Assign { target, op, value } => self.assign(target, *op, value, stmt.span),
            StmtKind::Return(value) => self.ret(value.as_ref(), stmt.span),
            StmtKind::If {
                branches,
                otherwise,
            } => self.if_stmt(branches, otherwise.as_ref()),
            StmtKind::While {
                label,
                condition,
                body,
            } => self.while_stmt(label.as_deref(), condition, body),
            StmtKind::Repeat { label, body, until } => {
                self.repeat_stmt(label.as_deref(), body, until)
            }
            StmtKind::Break(label) => self.leave(label.as_deref(), Exit::Break, stmt.span),
            StmtKind::Continue(label) => self.leave(label.as_deref(), Exit::Continue, stmt.span),
            StmtKind::Match { scrutinee, arms } => self.match_stmt(scrutinee, arms),
            // LR26: nothing runs here. The expression is lowered again at
            // every way out of the scope it was written in.
            StmtKind::Defer(expr) => self
                .deferred
                .last_mut()
                .expect("a scope is open")
                .push(expr.clone()),
            // LR29.2: `unsafe` is a promise the checker made the caller keep.
            // Nothing about what the block does changes here.
            StmtKind::Unsafe(block) => self.block(block),
            StmtKind::Expr(expr) => {
                self.expr(expr, None);
            }
            StmtKind::Error => {}
            _ => self.gap(stmt.span, "a statement"),
        }
    }

    // -- control flow -----------------------------------------------------

    /// LR10.1: each condition is tested in turn, and the first that holds
    /// runs its block. What every path that reaches the end agrees on carries
    /// through; what it does not becomes a parameter of the block they meet
    /// in.
    fn if_stmt(&mut self, branches: &[Branch], otherwise: Option<&Block>) {
        let join = self.function.add_block();
        let mut arrivals = Vec::new();

        for branch in branches {
            let condition = self.expr(&branch.condition, Some(&Ty::Bool));
            let then = self.function.add_block();
            let next = self.function.add_block();
            self.terminate(Terminator::Branch {
                condition,
                then: Target::to(then),
                otherwise: Target::to(next),
            });

            let saved = self.defs.clone();
            self.switch_to(then);
            self.block(&branch.body);
            if !self.left {
                arrivals.push(Arrival {
                    block: self.current,
                    defs: self.defs.clone(),
                });
            }

            self.defs = saved;
            self.switch_to(next);
        }

        if let Some(otherwise) = otherwise {
            self.block(otherwise);
        }
        if !self.left {
            arrivals.push(Arrival {
                block: self.current,
                defs: self.defs.clone(),
            });
        }

        self.join(arrivals, join);
    }

    /// LR10.2: the condition is tested before each pass.
    fn while_stmt(&mut self, label: Option<&str>, condition: &Expr, body: &Block) {
        let carried = self.carried(body);
        let header = self.function.add_block();
        self.jump_to(header, &carried);

        self.switch_to(header);
        self.add_params(header, &carried);
        self.bind_params(header, &carried);
        let entering = self.defs.clone();

        let condition = self.expr(condition, Some(&Ty::Bool));
        let inside = self.function.add_block();
        let exit = self.function.add_block();
        let leaving: Vec<Value> = carried.iter().map(|var| self.defs[var]).collect();
        self.add_params(exit, &carried);
        self.terminate(Terminator::Branch {
            condition,
            then: Target::to(inside),
            otherwise: Target::new(exit, leaving),
        });

        self.switch_to(inside);
        self.defs = entering.clone();
        self.loops.push(Loop {
            label: label.map(ToOwned::to_owned),
            again: Some(header),
            exit,
            carried: carried.clone(),
            depth: self.scopes.len(),
        });
        self.block(body);
        if !self.left {
            self.jump_to(header, &carried);
        }
        self.loops.pop();

        self.switch_to(exit);
        self.defs = entering;
        self.bind_params(exit, &carried);
    }

    /// LR10.3: the body runs before the condition is tested, so the loop runs
    /// at least once, and the condition is part of the body's scope.
    fn repeat_stmt(&mut self, label: Option<&str>, body: &Block, until: &Expr) {
        let carried = self.carried(body);
        let inside = self.function.add_block();
        self.jump_to(inside, &carried);

        let exit = self.function.add_block();
        self.add_params(inside, &carried);

        self.switch_to(inside);
        self.bind_params(inside, &carried);
        let entering = self.defs.clone();

        // LR10.3: `until` reads what the body declared, so it is lowered
        // inside the body's scope rather than in a block of its own.
        let depth = self.scopes.len();
        self.open();
        self.loops.push(Loop {
            label: label.map(ToOwned::to_owned),
            again: None,
            exit,
            carried: carried.clone(),
            depth,
        });
        for stmt in &body.stmts {
            if self.left {
                break;
            }
            self.stmt(stmt);
        }

        if !self.left {
            let condition = self.expr(until, Some(&Ty::Bool));
            // LR26: the scope ends here whichever way the branch goes, so
            // what it deferred runs once, before either.
            self.unwind(depth);
            let leaving: Vec<Value> = carried.iter().map(|var| self.defs[var]).collect();
            self.add_params(exit, &carried);
            self.terminate(Terminator::Branch {
                condition,
                then: Target::new(exit, leaving.clone()),
                otherwise: Target::new(inside, leaving),
            });
        } else {
            self.add_params(exit, &carried);
        }
        self.loops.pop();
        self.scopes.pop();
        self.deferred.pop();

        self.switch_to(exit);
        self.defs = entering;
        self.bind_params(exit, &carried);
    }

    /// LR16.1: the cases are tried in the order they are written, and the
    /// first whose pattern matches and whose guard holds runs.
    fn match_stmt(&mut self, scrutinee: &Expr, arms: &[MatchArm]) {
        let subject = self.expr(scrutinee, None);
        let join = self.function.add_block();
        let entering = self.defs.clone();
        let mut arrivals = Vec::new();

        for arm in arms {
            let next = self.function.add_block();
            self.open();
            self.arm(subject, arm, next);

            match &arm.body {
                ArmBody::Block(body) => self.block(body),
                ArmBody::Expr(value) => {
                    self.expr(value, None);
                }
            }
            if !self.left {
                arrivals.push(Arrival {
                    block: self.current,
                    defs: self.defs.clone(),
                });
            }

            self.close();
            self.switch_to(next);
            self.defs = entering.clone();
        }

        // LR16.4: the checker proved the cases cover every value, so control
        // cannot reach past the last one.
        self.terminate(Terminator::Trap(Trap::Unreachable));
        self.join(arrivals, join);
    }

    /// Tests one case, and where it does not hold leaves for `next`.
    ///
    /// Where it does hold, lowering carries on in the block the case's
    /// bindings are in scope in.
    fn arm(&mut self, subject: Value, arm: &MatchArm, next: BlockId) {
        self.test(subject, &arm.pattern, next);

        // LR16.3: a guard is tested after the pattern bound what it binds,
        // because the guard reads those bindings.
        if let Some(guard) = &arm.guard {
            let body = self.function.add_block();
            let condition = self.expr(guard, Some(&Ty::Bool));
            self.terminate(Terminator::Branch {
                condition,
                then: Target::to(body),
                otherwise: Target::to(next),
            });
            self.switch_to(body);
        }
    }

    /// Tests `subject` against `pattern`, leaving for `fail` where it does not
    /// match, and binding what it binds where it does (LR16.2).
    fn test(&mut self, subject: Value, pattern: &Pattern, fail: BlockId) {
        let span = pattern.span;
        match &pattern.kind {
            // Both match anything, so neither branches.
            PatternKind::Wildcard => {}
            PatternKind::Binding(name) => {
                let var = self.declare(name);
                self.defs.insert(var, subject);
            }

            PatternKind::Or(alternatives) => {
                let mut held: Option<Value> = None;
                for alternative in alternatives {
                    let Some(test) = self.decides(subject, alternative) else {
                        self.gap(span, "an alternative that binds inside an or-pattern");
                        return;
                    };
                    held = Some(match held {
                        None => test,
                        Some(earlier) => self.emit(
                            InstKind::Binary {
                                op: BinaryOp::BitOr,
                                left: earlier,
                                right: test,
                            },
                            Ty::Bool,
                            span,
                        ),
                    });
                }
                if let Some(test) = held {
                    self.check(test, fail);
                }
            }

            PatternKind::Path { segments, payload } => {
                let Some(name) = segments.last() else {
                    self.gap(span, "a path pattern naming nothing");
                    return;
                };
                let held = self.function.type_of(subject).clone();

                match self.variant_of(&held, name) {
                    Some(tag) => {
                        let test = self.tag_test(subject, tag, span);
                        self.check(test, fail);
                        self.bind_payload(subject, tag, payload.as_ref(), fail, span);
                    }
                    // LR16.2: a path naming a struct rather than a variant
                    // tests nothing, and reads the fields it lists.
                    None => match payload {
                        Some(Payload::Record { fields, .. }) => {
                            self.bind_fields(subject, fields, fail, span);
                        }
                        _ => self.gap(span, "a path pattern the compiler could not resolve"),
                    },
                }
            }

            PatternKind::Tuple(members) => {
                let held = self.function.type_of(subject).clone();
                let Ty::Tuple(types) = held else {
                    self.gap(span, "a tuple pattern over something that is not a tuple");
                    return;
                };
                if types.len() != members.len() {
                    self.gap(span, "a tuple pattern of another length");
                    return;
                }
                for (index, (member, ty)) in members.iter().zip(types).enumerate() {
                    let index = u32::try_from(index).expect("member count fits in u32");
                    let element = self.emit(
                        InstKind::GetElement {
                            tuple: subject,
                            index,
                        },
                        ty,
                        span,
                    );
                    self.test(element, member, fail);
                }
            }

            PatternKind::Literal(_) => match self.decides(subject, pattern) {
                Some(test) => self.check(test, fail),
                None => self.gap(span, "a literal pattern the compiler could not compare"),
            },

            PatternKind::Error => {}
            _ => self.gap(span, "a pattern"),
        }
    }

    /// The test a pattern comes down to, where it is one test and binds
    /// nothing. `None` for every pattern that is more than that.
    fn decides(&mut self, subject: Value, pattern: &Pattern) -> Option<Value> {
        let span = pattern.span;
        match &pattern.kind {
            PatternKind::Literal(literal) => {
                let held = self.function.type_of(subject).clone();
                let value = self.expr(literal, Some(&held));
                Some(self.emit(
                    InstKind::Binary {
                        op: BinaryOp::Equal,
                        left: subject,
                        right: value,
                    },
                    Ty::Bool,
                    span,
                ))
            }
            PatternKind::Path {
                segments,
                payload: None,
            } => {
                let held = self.function.type_of(subject).clone();
                let tag = self.variant_of(&held, segments.last()?)?;
                Some(self.tag_test(subject, tag, span))
            }
            _ => None,
        }
    }

    /// Whether `subject` holds the variant `tag` names (LR16.2).
    fn tag_test(&mut self, subject: Value, tag: u32, span: Span) -> Value {
        let held = self.emit(InstKind::GetTag { value: subject }, Ty::INT, span);
        let wanted = self.emit(InstKind::Const(Const::Int(u64::from(tag))), Ty::INT, span);
        self.emit(
            InstKind::Binary {
                op: BinaryOp::Equal,
                left: held,
                right: wanted,
            },
            Ty::Bool,
            span,
        )
    }

    /// Carries on where `test` held, and leaves for `fail` where it did not.
    fn check(&mut self, test: Value, fail: BlockId) {
        let held = self.function.add_block();
        self.terminate(Terminator::Branch {
            condition: test,
            then: Target::to(held),
            otherwise: Target::to(fail),
        });
        self.switch_to(held);
    }

    /// Matches what a variant carries, once its tag has proved the variant
    /// (LR15.2, LR16.2).
    fn bind_payload(
        &mut self,
        subject: Value,
        variant: u32,
        payload: Option<&Payload>,
        fail: BlockId,
        span: Span,
    ) {
        let Some(payload) = payload else {
            return;
        };
        let held = self.function.type_of(subject).clone();
        let Some(carried) = self.payload_of(&held, variant) else {
            self.gap(span, "a variant whose payload has no type");
            return;
        };

        match payload {
            Payload::Tuple(patterns) => {
                if patterns.len() != carried.len() {
                    self.gap(span, "a payload pattern of another length");
                    return;
                }
                for (index, (pattern, ty)) in patterns.iter().zip(carried).enumerate() {
                    let field = u32::try_from(index).expect("field count fits in u32");
                    let value = self.emit(
                        InstKind::GetPayload {
                            value: subject,
                            variant,
                            field,
                        },
                        ty,
                        span,
                    );
                    self.test(value, pattern, fail);
                }
            }
            Payload::Record { fields, .. } => {
                let Some(names) = self.payload_names(&held, variant) else {
                    self.gap(span, "a payload whose fields have no names");
                    return;
                };
                for written in fields {
                    let Some(index) = names.iter().position(|name| *name == written.field) else {
                        self.gap(written.span, "a payload field the compiler could not find");
                        continue;
                    };
                    let field = u32::try_from(index).expect("field count fits in u32");
                    let value = self.emit(
                        InstKind::GetPayload {
                            value: subject,
                            variant,
                            field,
                        },
                        carried[index].clone(),
                        written.span,
                    );
                    self.bind_field(value, written, fail);
                }
            }
        }
    }

    /// Matches the fields a struct or record pattern lists (LR16.2).
    fn bind_fields(&mut self, subject: Value, fields: &[FieldPattern], fail: BlockId, span: Span) {
        let held = self.function.type_of(subject).clone();
        let Some(declared) = self.fields_of(&held) else {
            self.gap(span, "a record pattern over a type with no fields");
            return;
        };

        for written in fields {
            let Some(index) = declared.iter().position(|(name, _)| *name == written.field) else {
                self.gap(written.span, "a field the compiler could not find");
                continue;
            };
            let field = u32::try_from(index).expect("field count fits in u32");
            let value = self.emit(
                InstKind::GetField {
                    object: subject,
                    field,
                },
                declared[index].1.clone(),
                written.span,
            );
            self.bind_field(value, written, fail);
        }
    }

    /// One field of a record pattern: matched against a pattern where it has
    /// one, and bound under the name it is written with otherwise (LR16.2).
    fn bind_field(&mut self, value: Value, written: &FieldPattern, fail: BlockId) {
        match &written.pattern {
            Some(pattern) => self.test(value, pattern, fail),
            None => {
                let name = written.bound_as.as_ref().unwrap_or(&written.field);
                let var = self.declare(name);
                self.defs.insert(var, value);
            }
        }
    }

    /// The names of what a variant carries, in the order it declares them.
    fn payload_names(&self, ty: &Ty, variant: u32) -> Option<Vec<String>> {
        let Ty::Named { id, .. } = ty else {
            return None;
        };
        let Shape::Enum(enumeration) = &self.context.program.nominal(*id).shape else {
            return None;
        };
        let held = enumeration.variants.get(variant as usize)?;
        Some(held.fields.iter().map(|field| field.name.clone()).collect())
    }

    /// LR10.6, LR10.7: `break` leaves the loop and `continue` starts its next
    /// pass, either the innermost one or the one a label names.
    fn leave(&mut self, label: Option<&str>, exit: Exit, span: Span) {
        let found = self.loops.iter().rev().find(|held| match label {
            Some(label) => held.label.as_deref() == Some(label),
            None => true,
        });

        let Some(found) = found else {
            self.gap(span, "leaving a loop the compiler could not find");
            return;
        };

        let block = match exit {
            Exit::Break => Some(found.exit),
            Exit::Continue => found.again,
        };
        let carried = found.carried.clone();
        let depth = found.depth;

        let Some(block) = block else {
            // LR10.3: a `repeat` condition reads what the body declared, so
            // it is lowered at the end of the body rather than in a block a
            // `continue` could jump to. Reaching it from the middle needs a
            // rule about what a binding declared after the `continue` holds,
            // and there is none to lower to.
            self.gap(span, "`continue` inside `repeat`");
            return;
        };
        // LR26: leaving a loop leaves every scope inside it, so each one runs
        // what it deferred, innermost first.
        self.unwind_from(depth);
        self.jump_to(block, &carried);
    }

    /// Gives `block` a parameter for each carried binding, typed as the
    /// binding is now.
    fn add_params(&mut self, block: BlockId, carried: &[Var]) {
        for var in carried {
            let ty = self.function.type_of(self.defs[var]).clone();
            self.function.add_block_param(block, ty);
        }
    }

    /// Points each carried binding at the parameter `block` receives it in.
    fn bind_params(&mut self, block: BlockId, carried: &[Var]) {
        let params = self.function.block(block).params.clone();
        for (var, param) in carried.iter().zip(params) {
            self.defs.insert(*var, param);
        }
    }

    fn jump_to(&mut self, block: BlockId, carried: &[Var]) {
        let args = carried.iter().map(|var| self.defs[var]).collect();
        self.terminate(Terminator::Jump(Target::new(block, args)));
    }

    /// Merges the paths that reached the end of a construct into `join`.
    ///
    /// A binding every path agrees on carries through. One they do not
    /// becomes a parameter of `join`, and each path passes what it holds,
    /// which is a phi written where the jump can see it.
    fn join(&mut self, arrivals: Vec<Arrival>, join: BlockId) {
        if arrivals.is_empty() {
            // LR50: every path left, so nothing after this runs.
            self.switch_to(join);
            self.terminate(Terminator::Trap(Trap::Unreachable));
            return;
        }

        let visible: Vec<Var> = self
            .scopes
            .iter()
            .flatten()
            .map(|(_, var)| *var)
            .filter(|var| {
                arrivals
                    .iter()
                    .all(|arrival| arrival.defs.contains_key(var))
            })
            .collect();

        let mut merged = HashMap::new();
        let mut parameters = Vec::new();
        for var in visible {
            let first = arrivals[0].defs[&var];
            if arrivals.iter().all(|arrival| arrival.defs[&var] == first) {
                merged.insert(var, first);
            } else {
                let ty = self.function.type_of(first).clone();
                let param = self.function.add_block_param(join, ty);
                merged.insert(var, param);
                parameters.push(var);
            }
        }

        for arrival in &arrivals {
            let args = parameters.iter().map(|var| arrival.defs[var]).collect();
            self.function.block_mut(arrival.block).term =
                Some(Terminator::Jump(Target::new(join, args)));
        }

        self.switch_to(join);
        self.defs = merged;
    }

    /// The bindings a loop body may write to, which are the ones its blocks
    /// have to pass along (LR5.4).
    ///
    /// A name declared inside the body resolves to nothing out here and is
    /// left out. A name the body shadows resolves to the outer binding, which
    /// carries one value further than it needs to and never one too few.
    fn carried(&self, body: &Block) -> Vec<Var> {
        let mut names = Vec::new();
        assigned(body, &mut names);

        let mut carried = Vec::new();
        for name in names {
            if let Some(var) = self.lookup(&name)
                && self.defs.contains_key(&var)
                && !carried.contains(&var)
            {
                carried.push(var);
            }
        }
        carried
    }

    fn switch_to(&mut self, block: BlockId) {
        self.current = block;
        self.left = false;
    }

    fn local(
        &mut self,
        binding: &Binding,
        ty: Option<&luar_ast::Type>,
        value: Option<&Expr>,
        span: Span,
    ) {
        let Binding::Name(name) = binding else {
            self.gap(span, "a destructuring binding");
            return;
        };

        // LR5.1: a declaration with a type takes it, and one without takes
        // what its initializer holds. The checker settled which, so lowering
        // reads that rather than resolving the annotation again.
        let _ = ty;
        let declared = self.declared_type(span);

        match value {
            Some(value) => {
                let held = self.expr(value, declared.as_ref());
                let var = self.declare(name);
                self.defs.insert(var, held);
            }
            None => {
                // LR5.1: nothing has been written yet, and the checker proved
                // nothing reads it before something does.
                self.declare(name);
            }
        }
    }

    /// The type the binding declared at `span` holds.
    fn declared_type(&mut self, span: Span) -> Option<Ty> {
        let ty = self.context.facts.binding(span)?.clone();
        match types::convert(&ty, self.context.ids) {
            Ok(converted) => Some(converted),
            Err(refused) => {
                self.gap(span, refused);
                None
            }
        }
    }

    fn assign(&mut self, target: &Expr, op: Option<AstBinary>, value: &Expr, span: Span) {
        let ExprKind::Name(name) = &target.kind else {
            self.gap(span, "an assignment to something other than a name");
            return;
        };
        let Some(var) = self.lookup(name) else {
            self.gap(span, "an assignment to a name from another scope");
            return;
        };

        let wanted = self.function.type_of(self.defs[&var]).clone();

        let held = match op {
            // LR5.4: a compound assignment reads the target, applies the
            // operator, and writes the result back.
            Some(op) => {
                let left = self.defs[&var];
                let right = self.expr(value, Some(&wanted));
                match binary_op(op) {
                    Some(op) => {
                        self.emit(InstKind::Binary { op, left, right }, wanted.clone(), span)
                    }
                    None => self.missing(span, "a compound assignment with this operator"),
                }
            }
            None => self.expr(value, Some(&wanted)),
        };

        self.defs.insert(var, held);
    }

    fn ret(&mut self, value: Option<&Expr>, span: Span) {
        let result = self.function.result.clone();
        let value = match value {
            Some(expr) => self.expr(expr, Some(&result)),
            None => self.emit(InstKind::Const(Const::Unit), Ty::Unit, span),
        };
        // LR26: a `return` leaves every scope the function has open, so
        // everything they deferred runs, innermost first. The value is
        // already worked out, so nothing a deferred expression does changes
        // what is returned.
        self.unwind_from(0);
        self.terminate(Terminator::Return(value));
    }

    // -- expressions ------------------------------------------------------

    /// Lowers `expr`, and gives back the value it produces.
    ///
    /// `wanted` is the type context asks for, where the source states one. It
    /// is what a literal takes (LR39) and what decides whether a value has to
    /// be wrapped to fill an optional (LR8).
    fn expr(&mut self, expr: &Expr, wanted: Option<&Ty>) -> Value {
        let value = self.expr_value(expr, wanted);
        match wanted {
            Some(wanted) => self.coerce(value, wanted, expr.span),
            None => value,
        }
    }

    fn expr_value(&mut self, expr: &Expr, wanted: Option<&Ty>) -> Value {
        let span = expr.span;
        match &expr.kind {
            ExprKind::Nil => {
                let ty = wanted.cloned().unwrap_or(Ty::Nil);
                self.emit(InstKind::Const(Const::Nil), ty, span)
            }
            ExprKind::Bool(value) => {
                self.emit(InstKind::Const(Const::Bool(*value)), Ty::Bool, span)
            }
            ExprKind::Integer(value) => {
                let ty = self.numeric(wanted, span);
                self.emit(InstKind::Const(Const::Int(*value)), ty, span)
            }
            ExprKind::Float(value) => {
                let ty = self.numeric(wanted, span);
                self.emit(InstKind::Const(Const::Float(*value)), ty, span)
            }
            ExprKind::String(value) => {
                self.emit(InstKind::Const(Const::Str(value.clone())), Ty::Str, span)
            }
            ExprKind::ByteString(value) => self.emit(
                InstKind::Const(Const::Bytes(value.clone())),
                Ty::Bytes,
                span,
            ),
            ExprKind::Char(value) => {
                self.emit(InstKind::Const(Const::Char(*value)), Ty::Char, span)
            }

            ExprKind::Name(name) => match self.lookup(name) {
                Some(var) => self.defs[&var],
                None => self.missing(span, "a name that is not a local binding"),
            },

            ExprKind::Unary { op, operand } => {
                let ty = self.recorded(span);
                let operand = self.expr(operand, Some(&ty));
                let op = match op {
                    AstUnary::Not => UnaryOp::Not,
                    AstUnary::Negate => UnaryOp::Negate,
                    AstUnary::BitNot => UnaryOp::BitNot,
                };
                self.emit(InstKind::Unary { op, operand }, ty, span)
            }

            ExprKind::Binary {
                op, left, right, ..
            } => self.binary(*op, left, right, span),

            ExprKind::Call {
                callee,
                method,
                args,
                ..
            } => self.call(callee, method.as_deref(), args, span),

            ExprKind::Record { path, fields } => self.record(path, fields, wanted, span),
            ExprKind::List(values) => self.list(values, wanted, span),
            ExprKind::Map(entries) => self.map(entries, wanted, span),
            ExprKind::Index {
                receiver,
                index,
                optional,
            } => self.index(receiver, index, *optional, span),
            ExprKind::Field {
                receiver,
                name,
                optional,
            } => self.field(receiver, name, *optional, span),
            ExprKind::Tuple(members) => {
                let types = match wanted {
                    Some(Ty::Tuple(types)) => types.clone(),
                    _ => match self.recorded(span) {
                        Ty::Tuple(types) => types,
                        _ => return self.missing(span, "a tuple whose members have no type"),
                    },
                };
                if types.len() != members.len() {
                    return self.missing(span, "a tuple of a length the checker did not agree on");
                }
                let values = members
                    .iter()
                    .zip(&types)
                    .map(|(member, ty)| self.expr(member, Some(ty)))
                    .collect();
                self.emit(InstKind::MakeTuple(values), Ty::Tuple(types), span)
            }

            ExprKind::Cast { value, .. } => {
                // LR33: `as` converts between numeric types, and the type it
                // converts to is the type of the whole expression.
                let to = self.recorded(span);
                let value = self.expr(value, None);
                self.emit(
                    InstKind::Convert {
                        value,
                        to: to.clone(),
                    },
                    to,
                    span,
                )
            }

            ExprKind::Error => self.missing(span, "an expression that did not parse"),

            _ => self.missing(span, "an expression"),
        }
    }

    /// The type a numeric literal takes: what context asked for, or what the
    /// checker settled it to where nothing did (LR39).
    fn numeric(&mut self, wanted: Option<&Ty>, span: Span) -> Ty {
        match wanted {
            Some(Ty::Optional(inner)) => (**inner).clone(),
            Some(wanted) => wanted.clone(),
            None => self.recorded(span),
        }
    }

    fn binary(&mut self, op: AstBinary, left: &Expr, right: &Expr, span: Span) -> Value {
        // LR8: comparing against `nil` asks whether an optional holds
        // anything, which is the check that settles it.
        if matches!(op, AstBinary::Equal | AstBinary::NotEqual) {
            for (value, other) in [(left, right), (right, left)] {
                if matches!(other.kind, ExprKind::Nil)
                    && self.known_type(value).is_some_and(|ty| ty.is_optional())
                {
                    let value = self.expr(value, None);
                    let held = self.emit(InstKind::IsSome { value }, Ty::Bool, span);
                    return match op {
                        AstBinary::NotEqual => held,
                        _ => self.emit(
                            InstKind::Unary {
                                op: UnaryOp::Not,
                                operand: held,
                            },
                            Ty::Bool,
                            span,
                        ),
                    };
                }
            }
        }

        match op {
            AstBinary::And | AstBinary::Or => self.logical(op == AstBinary::And, left, right, span),
            AstBinary::Coalesce => self.coalesce(left, right, span),
            _ => {
                let Some(lowered) = binary_op(op) else {
                    return self.missing(span, "a binary operator");
                };
                let operand = self.operand_type(left, right);
                // Arithmetic on one type produces it (LR39), which is the
                // answer where the checker had no name for the operands.
                let ty = match self.maybe_recorded(span) {
                    Some(recorded) => recorded,
                    None => operand.clone(),
                };
                // LR55: the left operand is evaluated first.
                let left = self.expr(left, Some(&operand));
                let right = self.expr(right, Some(&operand));
                self.emit(
                    InstKind::Binary {
                        op: lowered,
                        left,
                        right,
                    },
                    ty,
                    span,
                )
            }
        }
    }

    /// LR9.1: a call passes an argument for every parameter, at the type that
    /// parameter takes.
    ///
    /// LR55: the arguments are evaluated left to right as they are written,
    /// whatever parameter each one fills, and the defaults that fill the rest
    /// run after them in the order their parameters were declared (LR9.4).
    fn call(
        &mut self,
        callee: &Expr,
        method: Option<&str>,
        args: &[Argument],
        span: Span,
    ) -> Value {
        // LR15.3: a variant with a payload is written like a call and builds
        // a value, so it reaches no function and the checker recorded none.
        if let ExprKind::Field {
            receiver,
            name: variant,
            ..
        } = &callee.kind
            && let ExprKind::Name(written) = &receiver.kind
            && self.lookup(written).is_none()
        {
            let ty = self.recorded(span);
            if let Some(tag) = self.variant_of(&ty, variant) {
                return self.construct(ty, tag, args, span);
            }
        }

        let Some(declaration) = self.context.facts.call(span) else {
            return self.missing(span, "a call the checker did not resolve");
        };

        // LR12.2: `receiver:method(x)` is `Type.method(receiver, x)` written
        // short, so the receiver is the first argument either way.
        let receiver = method.map(|_| self.expr(callee, None));

        if let Some(virtual_) = self.context.virtuals.get(&declaration).copied() {
            return self.dispatch(virtual_, receiver, args, span);
        }

        let Some(reached) = self.context.callees.get(&declaration) else {
            return self.missing(span, "a call to a function with no body");
        };

        if reached.generic {
            // LR19: the call worked out what fills each type parameter, and
            // monomorphization needs to be told which. Nothing carries that
            // from the checker yet.
            return self.missing(span, "a call to a generic function");
        }
        if reached.params.iter().any(|param| param.variadic) {
            return self.missing(span, "a call to a variadic function");
        }

        let id = reached.id;
        let takes_self = reached.takes_self;
        let wanted: Vec<Ty> = reached
            .params
            .iter()
            .map(|param| param.ty.clone())
            .collect();
        let names: Vec<String> = reached
            .params
            .iter()
            .map(|param| param.name.clone())
            .collect();
        let defaults: Vec<Option<Expr>> = reached
            .params
            .iter()
            .map(|param| param.default.clone())
            .collect();

        let mut filled: Vec<Option<Value>> = vec![None; wanted.len()];
        let mut position = 0;
        for argument in args {
            let slot = match &argument.name {
                // LR9.5: a named argument names the parameter it fills.
                Some(name) => names.iter().position(|param| param == name),
                None => {
                    let slot = position;
                    position += 1;
                    Some(slot).filter(|slot| *slot < wanted.len())
                }
            };
            let value = self.expr(&argument.value, slot.map(|slot| &wanted[slot]));
            if let Some(slot) = slot {
                filled[slot] = Some(value);
            }
        }

        for (slot, default) in defaults.iter().enumerate() {
            if filled[slot].is_some() {
                continue;
            }
            let Some(default) = default else {
                return self.missing(span, "a call with no argument for a parameter");
            };
            filled[slot] = Some(self.expr(default, Some(&wanted[slot])));
        }

        let mut passed: Vec<Value> = Vec::with_capacity(filled.len() + 1);
        if takes_self {
            match receiver {
                Some(receiver) => passed.push(receiver),
                None => return self.missing(span, "a method call with no receiver"),
            }
        }
        for value in filled {
            match value {
                Some(value) => passed.push(value),
                None => return self.missing(span, "a call with no argument for a parameter"),
            }
        }

        let result = self.recorded(span);
        self.emit(
            InstKind::Call {
                callee: id,
                type_args: Vec::new(),
                args: passed,
            },
            result,
            span,
        )
    }

    /// LR12.1, LR12.2: a literal gives a value for every field, and a field
    /// with a default may be left out.
    ///
    /// LR55: the initializers run in the order they are written, whichever
    /// field each one fills, and the defaults that fill the rest run after
    /// them in the order the type declares them.
    fn record(
        &mut self,
        path: &[String],
        fields: &[FieldInit],
        wanted: Option<&Ty>,
        span: Span,
    ) -> Value {
        let ty = match self.recorded(span) {
            Ty::Never => match wanted {
                Some(wanted) => wanted.clone(),
                None => return self.missing(span, "a record literal with no type"),
            },
            recorded => recorded,
        };

        // LR15.3: a variant carrying named fields is written like a record
        // literal, and builds an enum value.
        if let Some(name) = path.last()
            && let Some(tag) = self.variant_of(&ty, name)
        {
            return self.construct_record(ty, tag, fields, span);
        }

        let Some(declared) = self.fields_of(&ty) else {
            return self.missing(span, "a record literal of a type with no fields");
        };

        let mut filled: Vec<Option<Value>> = vec![None; declared.len()];
        for init in fields {
            let slot = declared.iter().position(|(name, _)| *name == init.name);
            let value = self.expr(&init.value, slot.map(|slot| &declared[slot].1));
            if let Some(slot) = slot {
                filled[slot] = Some(value);
            }
        }

        for (slot, (_, held)) in declared.iter().enumerate() {
            if filled[slot].is_some() {
                continue;
            }

            let index = u32::try_from(slot).expect("field count fits in u32");
            let default = match &ty {
                Ty::Named { id, .. } => self.context.defaults.get(&(*id, index)).cloned(),
                _ => None,
            };

            filled[slot] = Some(match default {
                Some(default) => self.expr(&default, Some(held)),
                // LR12.1: a field a record leaves out is one nothing was
                // given for, which only an optional field may be.
                None if held.is_optional() => {
                    self.emit(InstKind::Const(Const::Nil), held.clone(), span)
                }
                None => return self.missing(span, "a literal with no value for a field"),
            });
        }

        let values = filled.into_iter().flatten().collect();
        self.emit(
            InstKind::MakeStruct {
                ty: ty.clone(),
                fields: values,
            },
            ty,
            span,
        )
    }

    /// LR12.2: `.` reads a field. LR8: `?.` reads one through a value that
    /// may hold nothing, and gives nothing back where it does.
    fn field(&mut self, receiver: &Expr, name: &str, optional: bool, span: Span) -> Value {
        // LR15.3: a variant with no payload is written like a field of the
        // enum, and builds a value rather than reading one.
        if let ExprKind::Name(written) = &receiver.kind
            && self.lookup(written).is_none()
        {
            let ty = self.recorded(span);
            if let Some(variant) = self.variant_of(&ty, name) {
                return self.emit(
                    InstKind::MakeEnum {
                        ty: ty.clone(),
                        variant,
                        payload: Vec::new(),
                    },
                    ty,
                    span,
                );
            }
        }

        let object = self.expr(receiver, None);
        let result = self.recorded(span);

        if !optional {
            let object = self.settled(object, span);
            let held = self.function.type_of(object).clone();
            let Some(index) = self.field_index(&held, name) else {
                return self.missing(span, "a member that is not a stored field");
            };
            return self.emit(
                InstKind::GetField {
                    object,
                    field: index,
                },
                result,
                span,
            );
        }

        let Ty::Optional(inner) = self.function.type_of(object).clone() else {
            return self.missing(span, "`?.` on a value that holds something already");
        };
        let Some(index) = self.field_index(&inner, name) else {
            return self.missing(span, "a member that is not a stored field");
        };
        let read = result.clone().without_optional();

        let present = self.function.add_block();
        let absent = self.function.add_block();
        let join = self.function.add_block();
        let there = self.emit(InstKind::IsSome { value: object }, Ty::Bool, span);
        self.terminate(Terminator::Branch {
            condition: there,
            then: Target::to(present),
            otherwise: Target::to(absent),
        });

        self.switch_to(present);
        let inside = self.emit(InstKind::Unwrap { value: object }, (*inner).clone(), span);
        let read = self.emit(
            InstKind::GetField {
                object: inside,
                field: index,
            },
            read,
            span,
        );
        let wrapped = self.coerce(read, &result, span);
        self.terminate(Terminator::Jump(Target::new(join, vec![wrapped])));

        self.switch_to(absent);
        let nothing = self.emit(InstKind::Const(Const::Nil), result.clone(), span);
        self.terminate(Terminator::Jump(Target::new(join, vec![nothing])));

        self.switch_to(join);
        self.function.add_block_param(join, result)
    }

    /// LR15.3: building an enum value from the payload the variant carries.
    fn construct(&mut self, ty: Ty, variant: u32, args: &[Argument], span: Span) -> Value {
        let Some(carried) = self.payload_of(&ty, variant) else {
            return self.missing(span, "a variant whose payload has no type");
        };
        if carried.len() != args.len() {
            return self.missing(span, "a variant given a payload of another length");
        }

        let payload = args
            .iter()
            .zip(&carried)
            .map(|(argument, held)| self.expr(&argument.value, Some(held)))
            .collect();

        self.emit(
            InstKind::MakeEnum {
                ty: ty.clone(),
                variant,
                payload,
            },
            ty,
            span,
        )
    }

    /// LR13.1, LR71: `[a, b]` fills a list or a fixed-size array, and which
    /// one it fills is what context asked for.
    fn list(&mut self, values: &[Expr], wanted: Option<&Ty>, span: Span) -> Value {
        let ty = self.settled_type(wanted, span);
        let element = match &ty {
            Ty::Builtin { args, .. } => args.first().cloned(),
            Ty::Array(element) => Some((**element).clone()),
            _ => None,
        };
        let Some(element) = element else {
            return self.missing(span, "a sequence literal whose elements have no type");
        };

        let values = values
            .iter()
            .map(|value| self.expr(value, Some(&element)))
            .collect();
        self.emit(InstKind::MakeList { element, values }, ty, span)
    }

    /// LR13.2: `Map { ... }` builds a map, by name or by computed key.
    fn map(&mut self, entries: &[MapEntry], wanted: Option<&Ty>, span: Span) -> Value {
        let ty = self.settled_type(wanted, span);
        let Ty::Builtin { args, .. } = &ty else {
            return self.missing(span, "a map literal whose entries have no type");
        };
        let (Some(key), Some(value)) = (args.first().cloned(), args.get(1).cloned()) else {
            return self.missing(span, "a map literal whose entries have no type");
        };

        let mut built = Vec::with_capacity(entries.len());
        for entry in entries {
            // LR55: an entry's key is written before its value, so it is
            // evaluated first.
            let held = match &entry.key {
                MapKey::Name(name) => {
                    self.emit(InstKind::Const(Const::Str(name.clone())), key.clone(), span)
                }
                MapKey::Computed(computed) => self.expr(computed, Some(&key)),
            };
            built.push((held, self.expr(&entry.value, Some(&value))));
        }

        self.emit(
            InstKind::MakeMap {
                key,
                value,
                entries: built,
            },
            ty,
            span,
        )
    }

    /// LR37: `x[i]` reads what the container holds at `i`. LR69: a map hands
    /// back an optional, because a key it does not hold is not a mistake.
    fn index(&mut self, receiver: &Expr, index: &Expr, optional: bool, span: Span) -> Value {
        if optional {
            return self.missing(span, "an optional index");
        }

        // LR55: the container is written before the index, so it is
        // evaluated first.
        let container = self.expr(receiver, None);
        let container = self.settled(container, span);
        let held = self.function.type_of(container).clone();
        let Ty::Builtin { args, .. } = &held else {
            return self.missing(span, "indexing something the compiler cannot index");
        };
        let key = args.first().cloned();

        // LR37: a list and an array are keyed by position, and only a map
        // states what it is keyed by.
        let wanted = match &held {
            Ty::Builtin {
                kind: Builtin::Map | Builtin::FrozenMap,
                ..
            } => key,
            _ => Some(Ty::Int(IntTy::Usize)),
        };

        let index = self.expr(index, wanted.as_ref());
        let result = self.recorded(span);
        self.emit(
            InstKind::GetIndex {
                receiver: container,
                index,
            },
            result,
            span,
        )
    }

    /// The type context asked for, or the one the checker settled on where
    /// nothing did.
    fn settled_type(&mut self, wanted: Option<&Ty>, span: Span) -> Ty {
        match wanted {
            Some(wanted) => wanted.clone(),
            None => self.recorded(span),
        }
    }

    /// LR15.3: building an enum value whose variant carries named fields.
    fn construct_record(
        &mut self,
        ty: Ty,
        variant: u32,
        fields: &[FieldInit],
        span: Span,
    ) -> Value {
        let (Some(names), Some(carried)) = (
            self.payload_names(&ty, variant),
            self.payload_of(&ty, variant),
        ) else {
            return self.missing(span, "a variant whose payload has no type");
        };

        let mut filled: Vec<Option<Value>> = vec![None; names.len()];
        for init in fields {
            let slot = names.iter().position(|name| *name == init.name);
            let value = self.expr(&init.value, slot.map(|slot| &carried[slot]));
            if let Some(slot) = slot {
                filled[slot] = Some(value);
            }
        }

        if filled.iter().any(Option::is_none) {
            return self.missing(span, "a variant with no value for a field it carries");
        }

        let payload = filled.into_iter().flatten().collect();
        self.emit(
            InstKind::MakeEnum {
                ty: ty.clone(),
                variant,
                payload,
            },
            ty,
            span,
        )
    }

    /// What a variant carries, in the order the enum declares it (LR15.2).
    fn payload_of(&self, ty: &Ty, variant: u32) -> Option<Vec<Ty>> {
        let Ty::Named { id, args } = ty else {
            return None;
        };
        if !args.is_empty() {
            // LR19: the payload of a generic enum is written in its type
            // parameters, and putting the arguments in their place is
            // monomorphization's job.
            return None;
        }
        let Shape::Enum(enumeration) = &self.context.program.nominal(*id).shape else {
            return None;
        };
        let held = enumeration.variants.get(variant as usize)?;
        Some(held.fields.iter().map(|field| field.ty.clone()).collect())
    }

    /// The fields a type stores, in the order it declares them.
    fn fields_of(&self, ty: &Ty) -> Option<Vec<(String, Ty)>> {
        match ty {
            Ty::Named { id, .. } => match &self.context.program.nominal(*id).shape {
                Shape::Struct(structure) => Some(
                    structure
                        .fields
                        .iter()
                        .map(|field| (field.name.clone(), field.ty.clone()))
                        .collect(),
                ),
                _ => None,
            },
            Ty::Record(fields) => Some(fields.clone()),
            _ => None,
        }
    }

    fn field_index(&self, ty: &Ty, name: &str) -> Option<u32> {
        let index = self
            .fields_of(ty)?
            .iter()
            .position(|(held, _)| held == name)?;
        u32::try_from(index).ok()
    }

    /// The tag of the variant `name` names, if `ty` is an enum with one
    /// (LR15).
    fn variant_of(&self, ty: &Ty, name: &str) -> Option<u32> {
        let Ty::Named { id, .. } = ty else {
            return None;
        };
        let Shape::Enum(enumeration) = &self.context.program.nominal(*id).shape else {
            return None;
        };
        let index = enumeration
            .variants
            .iter()
            .position(|variant| variant.name == name)?;
        u32::try_from(index).ok()
    }

    /// LR18.1: a call through an interface finds its implementation at
    /// runtime, until devirtualization proves there is only one.
    fn dispatch(
        &mut self,
        method: MethodId,
        receiver: Option<Value>,
        args: &[Argument],
        span: Span,
    ) -> Value {
        let Some(receiver) = receiver else {
            return self.missing(span, "an interface call with no receiver");
        };
        if args.iter().any(|argument| argument.name.is_some()) {
            return self.missing(span, "an interface call with named arguments");
        }

        let passed: Vec<Value> = args
            .iter()
            .map(|argument| self.expr(&argument.value, None))
            .collect();
        let result = self.recorded(span);
        self.emit(
            InstKind::CallVirtual {
                method,
                receiver,
                args: passed,
            },
            result,
            span,
        )
    }

    /// LR11.4, LR56: `and` does not evaluate its right operand where the left
    /// is false, and `or` does not where the left is true.
    fn logical(&mut self, all: bool, left: &Expr, right: &Expr, span: Span) -> Value {
        let left = self.expr(left, Some(&Ty::Bool));
        let rest = self.function.add_block();
        let join = self.function.add_block();
        let settled = self.emit(InstKind::Const(Const::Bool(!all)), Ty::Bool, span);

        let short = Target::new(join, vec![settled]);
        self.terminate(if all {
            Terminator::Branch {
                condition: left,
                then: Target::to(rest),
                otherwise: short,
            }
        } else {
            Terminator::Branch {
                condition: left,
                then: short,
                otherwise: Target::to(rest),
            }
        });

        self.switch_to(rest);
        let right = self.expr(right, Some(&Ty::Bool));
        self.terminate(Terminator::Jump(Target::new(join, vec![right])));

        self.switch_to(join);
        self.function.add_block_param(join, Ty::Bool)
    }

    /// LR8, LR56: `??` takes the left where it holds a value, and does not
    /// evaluate the right at all.
    fn coalesce(&mut self, left: &Expr, right: &Expr, span: Span) -> Value {
        let ty = self.recorded(span);
        let optional = Ty::Optional(Box::new(ty.clone()));
        let left = self.expr(left, Some(&optional));

        let present = self.function.add_block();
        let absent = self.function.add_block();
        let join = self.function.add_block();
        let held = self.emit(InstKind::IsSome { value: left }, Ty::Bool, span);
        self.terminate(Terminator::Branch {
            condition: held,
            then: Target::to(present),
            otherwise: Target::to(absent),
        });

        self.switch_to(present);
        let inside = self.emit(InstKind::Unwrap { value: left }, ty.clone(), span);
        self.terminate(Terminator::Jump(Target::new(join, vec![inside])));

        self.switch_to(absent);
        let fallback = self.expr(right, Some(&ty));
        self.terminate(Terminator::Jump(Target::new(join, vec![fallback])));

        self.switch_to(join);
        self.function.add_block_param(join, ty)
    }

    /// A value put where `wanted` is asked for.
    ///
    /// LR8: a `T` fills a `T?` by being wrapped, which is where the wrapping
    /// happens rather than at every site that could need it.
    fn coerce(&mut self, value: Value, wanted: &Ty, span: Span) -> Value {
        let held = self.function.type_of(value).clone();
        match wanted {
            Ty::Optional(inner) if held == **inner => {
                self.emit(InstKind::MakeSome { value }, wanted.clone(), span)
            }
            // LR18.1: a value used through an interface carries the
            // implementation to dispatch to. What it carries is a
            // representation nothing has decided yet.
            _ if held != *wanted && self.is_interface(wanted) => {
                self.gap(span, "a value used as an interface value");
                value
            }
            _ => value,
        }
    }

    fn is_interface(&self, ty: &Ty) -> bool {
        match ty {
            Ty::Named { id, .. } => {
                matches!(self.context.program.nominal(*id).shape, Shape::Interface(_))
            }
            _ => false,
        }
    }
}

/// The names `block` assigns to, anywhere inside it.
///
/// Over-approximating is safe: a name that turns out to be shadowed or
/// declared inside carries a value one block further than it needs to. Missing
/// one is not, because the block that merged the paths would then read a
/// value from the wrong pass.
fn assigned(block: &Block, out: &mut Vec<String>) {
    for stmt in &block.stmts {
        match &stmt.kind {
            StmtKind::Assign { target, .. } => {
                if let ExprKind::Name(name) = &target.kind {
                    out.push(name.clone());
                }
            }
            StmtKind::If {
                branches,
                otherwise,
            } => {
                for branch in branches {
                    assigned(&branch.body, out);
                }
                if let Some(otherwise) = otherwise {
                    assigned(otherwise, out);
                }
            }
            StmtKind::While { body, .. }
            | StmtKind::Repeat { body, .. }
            | StmtKind::For { body, .. }
            | StmtKind::Unsafe(body) => assigned(body, out),
            StmtKind::Match { arms, .. } => {
                for arm in arms {
                    if let ArmBody::Block(body) = &arm.body {
                        assigned(body, out);
                    }
                }
            }
            StmtKind::Conditional {
                branches,
                otherwise,
            } => {
                for (_, body) in branches {
                    assigned(body, out);
                }
                if let Some(otherwise) = otherwise {
                    assigned(otherwise, out);
                }
            }
            _ => {}
        }
    }
}

fn binary_op(op: AstBinary) -> Option<BinaryOp> {
    let lowered = match op {
        AstBinary::Add => BinaryOp::Add,
        AstBinary::Subtract => BinaryOp::Subtract,
        AstBinary::Multiply => BinaryOp::Multiply,
        AstBinary::Divide => BinaryOp::Divide,
        AstBinary::IntegerDivide => BinaryOp::IntegerDivide,
        AstBinary::Remainder => BinaryOp::Remainder,
        AstBinary::Power => BinaryOp::Power,
        AstBinary::Concat => BinaryOp::Concat,
        AstBinary::Equal => BinaryOp::Equal,
        AstBinary::NotEqual => BinaryOp::NotEqual,
        AstBinary::Less => BinaryOp::Less,
        AstBinary::LessEqual => BinaryOp::LessEqual,
        AstBinary::Greater => BinaryOp::Greater,
        AstBinary::GreaterEqual => BinaryOp::GreaterEqual,
        AstBinary::BitAnd => BinaryOp::BitAnd,
        AstBinary::BitOr => BinaryOp::BitOr,
        AstBinary::BitXor => BinaryOp::BitXor,
        AstBinary::ShiftLeft => BinaryOp::ShiftLeft,
        AstBinary::ShiftRight => BinaryOp::ShiftRight,
        AstBinary::And | AstBinary::Or | AstBinary::Coalesce => return None,
    };
    Some(lowered)
}
