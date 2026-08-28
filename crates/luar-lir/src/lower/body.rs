//! Lowering one function body.

use std::cell::Cell;
use std::collections::{HashMap, HashSet};

use luar_ast::{
    Argument, ArmBody, BinaryOp as AstBinary, Binding, Block, Branch, CatchClause, Expr, ExprKind,
    FieldInit, FieldPattern, FunctionBody, MapEntry, MapKey, MatchArm, Param, Pattern, PatternKind,
    Payload, Stmt, StmtKind, UnaryOp as AstUnary,
};
use luar_diagnostics::Span;
use luar_sema::check::protocol_of;
use luar_sema::facts::{CollectionMutation, Facts, Intrinsic, OverflowMethod};
use luar_sema::modules::ModuleId;

use luar_sema::types::Type;

use crate::inst::MethodId;
use crate::inst::{
    BinaryOp, Const, Inst, InstKind, Overflow, Target, Terminator, Trap, UnaryOp, Value,
};
use crate::lower::names;
use crate::lower::throws;
use crate::lower::types::{self, Ids};
use crate::lower::{Callee, CompilationMode, Gap, Property, thrown_or};
use crate::program::{BlockId, FuncId, Function, Program, Shape, SlotId};
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

/// What runs on the way out of a scope, in reverse order of registration
/// (LR25.3, LR26).
#[derive(Clone)]
enum Cleanup {
    Deferred(Expr),
    Finally(Block),
}

/// Where a thrown value goes (LR25.3).
#[derive(Clone)]
struct Handler {
    /// The block that decides which clause catches it. Its first parameter is
    /// the thrown value.
    block: BlockId,
    /// The first scope to unwind on the way there. The scopes outside it stay
    /// open, so a `finally` around the handler runs when the handler is done
    /// rather than on the way to it.
    frame: usize,
    /// The bindings the handler's block takes after the thrown value, which
    /// are the ones the guarded block writes to.
    carried: Vec<Var>,
}

/// What lowering a body needs from the rest of the program.
#[derive(Clone, Copy)]
pub(super) struct Context<'a> {
    /// The next function id nothing has taken. A closure takes one as it is
    /// lowered, because it is a function nothing declared (LR9.8).
    pub next_function: &'a Cell<u32>,
    pub facts: &'a Facts,
    pub mode: CompilationMode,
    pub ids: &'a Ids,
    /// What each function declaration became, by the span the checker
    /// recorded a call as reaching (LR40, LR76).
    pub callees: &'a HashMap<Span, Callee>,
    /// The interface methods, which have declarations and no bodies (LR18.1).
    pub virtuals: &'a HashMap<Span, MethodId>,
    /// The default written beside a field (LR12.2).
    pub defaults: &'a HashMap<(TypeId, u32), Expr>,
    /// The computed members of each type (LR43).
    pub properties: &'a HashMap<(TypeId, String), Property>,
    /// The declarations an exception can escape (LR25.3).
    pub throwing: &'a HashSet<Span>,
    pub program: &'a Program,
    /// The module the body is written in.
    pub module: ModuleId,
    /// Each module-level `const`, with the span of its declaration and its
    /// initializer (LR24).
    pub constants: &'a HashMap<(ModuleId, String), (Span, Expr)>,
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
    /// What each open scope runs on the way out, in the order it was written
    /// (LR25.3, LR26). One frame per entry in `scopes`.
    deferred: Vec<Vec<Cleanup>>,
    /// The `try` statements open around what is being lowered, innermost
    /// last. Empty where a thrown value leaves the function (LR25.3).
    handlers: Vec<Handler>,
    /// What the source says the function gives back. Where an exception can
    /// escape it, [`Function::result`] is that or what was thrown, and this
    /// is the half a `return` writes (LR25.3).
    declared: Ty,
    /// Whether an exception can escape this function (LR25.3).
    throws: bool,
    /// The value each binding currently holds.
    defs: HashMap<Var, Value>,
    /// The stack slot a binding whose address is taken lives in (LR72).
    slots: HashMap<Var, SlotId>,
    /// The module-level constants being read, outermost first (LR24).
    expanding: Vec<String>,
    next_var: u32,
    /// The loops open around what is being lowered, innermost last.
    loops: Vec<Loop>,
    /// The names something in this function assigns to, which are the ones a
    /// closure cannot capture by value (LR9.8).
    mutated: Vec<String>,
    /// The closures this body built, in the order they took their ids.
    made: Vec<(FuncId, Function)>,
    gaps: Vec<Gap>,
}

impl<'a> Body<'a> {
    pub(super) fn new(context: Context<'a>, mut function: Function, throws: bool) -> Self {
        let entry = function.entry;
        function.block_mut(entry).term = None;
        let declared = match (throws, &function.result) {
            (
                true,
                Ty::Builtin {
                    kind: Builtin::Result,
                    args,
                },
            ) => args.first().cloned().unwrap_or(Ty::Unit),
            _ => function.result.clone(),
        };
        Self {
            context,
            function,
            current: entry,
            left: false,
            scopes: vec![Vec::new()],
            deferred: vec![Vec::new()],
            handlers: Vec::new(),
            declared,
            throws,
            defs: HashMap::new(),
            slots: HashMap::new(),
            expanding: Vec::new(),
            next_var: 0,
            loops: Vec::new(),
            mutated: Vec::new(),
            made: Vec::new(),
            gaps: Vec::new(),
        }
    }

    /// Binds the entry block's parameters in order and lowers `block` into the
    /// function.
    /// A closure takes itself first and reads what it captured out of that
    /// object, so `captured` names those in the order they sit there (LR9.8).
    pub(super) fn lower(
        mut self,
        captured: Option<&[(String, Ty)]>,
        bindings: &[Binding],
        block: &Block,
    ) -> (Function, Vec<(FuncId, Function)>, Vec<Gap>) {
        assigned(block, &mut self.mutated);
        let mut params: Vec<Value> = self.function.block(self.function.entry).params.clone();
        if let Some(captured) = captured {
            let closure = params.remove(0);
            for (index, (name, ty)) in captured.iter().enumerate() {
                let field = u32::try_from(index + 1).expect("capture count fits in u32");
                let value = self.emit(
                    InstKind::GetField {
                        object: closure,
                        field,
                    },
                    ty.clone(),
                    block.span,
                );
                self.bind_value(&Binding::Name(name.clone()), value, block.span);
            }
        }
        for (binding, value) in bindings.iter().zip(params) {
            self.bind_value(binding, value, block.span);
        }

        self.block(block);

        // LR9.1: a body that runs off its end returns nothing, which is only a
        // value where the function writes no result.
        if !self.left {
            let span = block.span;
            let term = if self.declared == Ty::Unit {
                let unit = self.emit(InstKind::Const(Const::Unit), Ty::Unit, span);
                let returned = self.returned(unit, span);
                Terminator::Return(returned)
            } else {
                Terminator::Trap(Trap::Unreachable)
            };
            self.terminate(term);
        }

        (self.function, self.made, self.gaps)
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

    /// Emits an instruction that produces no value: one that is there for
    /// what it does.
    fn emit_void(&mut self, kind: InstKind, span: Span) {
        self.function.block_mut(self.current).insts.push(Inst {
            result: None,
            kind,
            span,
        });
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
    /// (LR25.3, LR26).
    fn unwind(&mut self, frame: usize) {
        for cleanup in self.deferred[frame].clone().iter().rev() {
            match cleanup {
                Cleanup::Deferred(call) => {
                    self.expr(call, None);
                }
                Cleanup::Finally(block) => {
                    self.block(block);
                    if self.left {
                        self.gap(block.span, "a `finally` that leaves where it is written");
                        return;
                    }
                }
            }
        }
    }

    /// Runs what every scope from `depth` outward deferred, innermost first,
    /// which is what leaving several of them at once does (LR26).
    fn unwind_from(&mut self, depth: usize) {
        for frame in (depth..self.scopes.len()).rev() {
            self.unwind(frame);
        }
    }

    /// LR24: a module-level `const` is its initializer, which is pure (LR79),
    /// worked out where the name is read.
    fn constant(&mut self, name: &str, wanted: Option<&Ty>, span: Span) -> Value {
        let key = (self.context.module, name.to_owned());
        let Some((declared, initializer)) = self.context.constants.get(&key).cloned() else {
            return self.missing(span, "a name that is not a local binding");
        };
        if self.expanding.iter().any(|held| held == name) {
            return self.missing(span, "a `const` that reads itself");
        }
        let declared = self.declared_type(declared);
        self.expanding.push(name.to_owned());
        let value = self.expr(&initializer, declared.as_ref().or(wanted));
        self.expanding.pop();
        value
    }

    /// What `var` holds now: its slot's contents where it has one, and its
    /// value otherwise (LR72).
    fn read_var(&mut self, var: Var, span: Span) -> Value {
        match self.slots.get(&var).copied() {
            Some(slot) => {
                let ty = self.function.slot_type(slot).clone();
                self.emit(InstKind::SlotGet { slot }, ty, span)
            }
            None => self.defs[&var],
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
    fn known_type(&mut self, expr: &Expr) -> Option<Ty> {
        if let ExprKind::Name(name) = &expr.kind
            && let Some(var) = self.lookup(name)
            && let Some(value) = self.defs.get(&var)
        {
            let held = self.function.type_of(*value).clone();
            // LR57: a name the checker proved holds something reads as
            // what it holds.
            if let Ty::Optional(inner) = &held
                && self.maybe_recorded(expr.span).as_ref() == Some(inner.as_ref())
            {
                return Some(inner.as_ref().clone());
            }
            return Some(held);
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
            StmtKind::For {
                label,
                bindings,
                iterable,
                body,
            } => self.for_stmt(label.as_deref(), bindings, iterable, body, stmt.span),
            StmtKind::Break(label) => self.leave(label.as_deref(), Exit::Break, stmt.span),
            StmtKind::Continue(label) => self.leave(label.as_deref(), Exit::Continue, stmt.span),
            StmtKind::Match { scrutinee, arms } => self.match_stmt(scrutinee, arms),
            // LR26: nothing runs here.
            StmtKind::Defer(expr) => self
                .deferred
                .last_mut()
                .expect("a scope is open")
                .push(Cleanup::Deferred(expr.clone())),
            StmtKind::Throw(value) => self.throw_stmt(value, stmt.span),
            StmtKind::Try {
                body,
                catches,
                finally,
            } => self.try_stmt(body, catches, finally.as_ref(), stmt.span),
            // LR29.2: `unsafe` is a promise the checker made the caller keep.
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

    /// LR10.4: a `for` over a range written in place counts from its lower
    /// bound up to its upper one, and runs zero times where the lower bound
    /// is the greater. LR10.5: one over a list counts through its indices,
    /// and one over a map or a set counts through its buckets and runs the
    /// body for each that is occupied. Anything else iterates through the
    /// protocol (LR35).
    fn for_stmt(
        &mut self,
        label: Option<&str>,
        bindings: &[Binding],
        iterable: &Expr,
        body: &Block,
        span: Span,
    ) {
        enum Source {
            Range { last: Value, inclusive: bool },
            Reversed { first: Value, inclusive: bool },
            List { receiver: Value, indexed: bool },
            Table(Value),
        }

        let carried = self.carried(body);
        let header = self.function.add_block();
        self.open();
        let (source, counter, first, element) = match (&iterable.kind, bindings) {
            (
                ExprKind::Range {
                    start: Some(start),
                    end: Some(end),
                    inclusive,
                },
                [Binding::Name(name)],
            ) => {
                let element = self
                    .declared_type(span)
                    .or_else(|| self.known_type(start))
                    .unwrap_or(Ty::Int(IntTy::I64));
                let first = self.expr(start, Some(&element));
                let last = self.expr(end, Some(&element));
                let source = Source::Range {
                    last,
                    inclusive: *inclusive,
                };
                (source, self.declare(name), first, element)
            }
            (ExprKind::Range { .. }, _) => {
                self.gap(span, "a range loop that does not bind one name");
                return;
            }
            (
                ExprKind::Call {
                    callee,
                    method: Some(method),
                    args,
                    ..
                },
                _,
            ) if method == "reversed" && args.is_empty() => {
                let ExprKind::Range {
                    start: Some(start),
                    end: Some(end),
                    inclusive,
                } = &callee.kind
                else {
                    self.gap(
                        span,
                        "`reversed()` on something other than a range written in place",
                    );
                    return;
                };
                let element = self
                    .declared_type(span)
                    .or_else(|| self.known_type(start))
                    .unwrap_or(Ty::Int(IntTy::I64));
                let first = self.expr(start, Some(&element));
                let last = self.expr(end, Some(&element));
                let source = Source::Reversed {
                    first,
                    inclusive: *inclusive,
                };
                (source, self.declare(""), last, element)
            }
            _ => {
                let (iterable, indexed) = match &iterable.kind {
                    ExprKind::Call {
                        callee,
                        method: Some(method),
                        args,
                        ..
                    } if method == "enumerated" && args.is_empty() => (callee.as_ref(), true),
                    _ => (iterable, false),
                };
                let receiver = self.expr(iterable, None);
                let source = match self.function.type_of(receiver) {
                    Ty::Builtin {
                        kind: Builtin::List | Builtin::FrozenList,
                        ..
                    } => Source::List { receiver, indexed },
                    Ty::Builtin {
                        kind: Builtin::Map | Builtin::FrozenMap | Builtin::Set | Builtin::FrozenSet,
                        ..
                    } => Source::Table(receiver),
                    _ => {
                        self.gap(
                            span,
                            "a `for` over something that is not a range or a collection",
                        );
                        return;
                    }
                };
                let zero = self.emit(InstKind::Const(Const::Int(0)), Ty::INT, span);
                (source, self.declare(""), zero, Ty::INT)
            }
        };

        self.defs.insert(counter, first);
        let mut passing = carried.clone();
        passing.push(counter);
        self.jump_to(header, &passing);

        self.switch_to(header);
        self.add_params(header, &passing);
        self.bind_params(header, &passing);
        let entering = self.defs.clone();

        let current = self.defs[&counter];
        let descending = matches!(source, Source::Reversed { .. });
        let (op, bound) = match source {
            Source::Range { last, inclusive } => {
                let op = if inclusive {
                    BinaryOp::LessEqual
                } else {
                    BinaryOp::Less
                };
                (op, last)
            }
            Source::Reversed { first, inclusive } => {
                let op = if inclusive {
                    BinaryOp::GreaterEqual
                } else {
                    BinaryOp::Greater
                };
                (op, first)
            }
            Source::List { receiver, .. } => (
                BinaryOp::Less,
                self.emit(InstKind::Length { receiver }, Ty::INT, span),
            ),
            Source::Table(receiver) => (
                BinaryOp::Less,
                self.emit(InstKind::Buckets { receiver }, Ty::INT, span),
            ),
        };
        let condition = self.emit(
            InstKind::Binary {
                op,
                left: current,
                right: bound,
            },
            Ty::Bool,
            span,
        );
        let inside = self.function.add_block();
        let step = self.function.add_block();
        let exit = self.function.add_block();
        let leaving: Vec<Value> = carried.iter().map(|held| self.defs[held]).collect();
        self.add_params(exit, &carried);
        self.add_params(step, &carried);
        self.terminate(Terminator::Branch {
            condition,
            then: Target::to(inside),
            otherwise: Target::new(exit, leaving.clone()),
        });

        self.switch_to(inside);
        self.defs = entering.clone();
        match source {
            Source::Range { .. } => {}
            Source::Reversed { inclusive, .. } => {
                let value = if inclusive {
                    current
                } else {
                    let one = self.emit(InstKind::Const(Const::Int(1)), element.clone(), span);
                    self.emit(
                        InstKind::Binary {
                            op: BinaryOp::Subtract,
                            left: current,
                            right: one,
                        },
                        element.clone(),
                        span,
                    )
                };
                if let Some(binding) = bindings.first() {
                    self.bind_value(binding, value, span);
                }
            }
            Source::List { receiver, indexed } => {
                let held = self.collection_args(receiver);
                let element = self.emit(
                    InstKind::GetIndex {
                        receiver,
                        index: current,
                    },
                    held.first().cloned().unwrap_or(Ty::Never),
                    span,
                );
                let yielded = if indexed {
                    vec![current, element]
                } else {
                    vec![element]
                };
                for (binding, value) in bindings.iter().zip(yielded) {
                    self.bind_value(binding, value, span);
                }
            }
            Source::Table(receiver) => {
                let occupied = self.emit(
                    InstKind::Occupied {
                        receiver,
                        index: current,
                    },
                    Ty::Bool,
                    span,
                );
                let found = self.function.add_block();
                self.terminate(Terminator::Branch {
                    condition: occupied,
                    then: Target::to(found),
                    otherwise: Target::new(step, leaving),
                });
                self.switch_to(found);

                let held = self.collection_args(receiver);
                let reads = [
                    InstKind::EntryKey {
                        receiver,
                        index: current,
                    },
                    InstKind::EntryValue {
                        receiver,
                        index: current,
                    },
                ];
                for ((binding, read), ty) in bindings.iter().zip(reads).zip(held) {
                    let value = self.emit(read, ty, span);
                    self.bind_value(binding, value, span);
                }
            }
        }
        self.loops.push(Loop {
            label: label.map(ToOwned::to_owned),
            again: Some(step),
            exit,
            carried: carried.clone(),
            depth: self.scopes.len(),
        });
        self.block(body);
        if !self.left {
            self.jump_to(step, &carried);
        }
        self.loops.pop();

        self.switch_to(step);
        self.defs = entering.clone();
        self.bind_params(step, &carried);
        let one = self.emit(InstKind::Const(Const::Int(1)), element.clone(), span);
        let next = self.emit(
            InstKind::Binary {
                op: if descending {
                    BinaryOp::Subtract
                } else {
                    BinaryOp::Add
                },
                left: current,
                right: one,
            },
            element,
            span,
        );
        self.defs.insert(counter, next);
        self.jump_to(header, &passing);
        self.close();

        self.switch_to(exit);
        self.defs = entering;
        self.bind_params(exit, &carried);
    }

    /// The type arguments of the collection `receiver` holds.
    fn collection_args(&self, receiver: Value) -> Vec<Ty> {
        match self.function.type_of(receiver) {
            Ty::Builtin { args, .. } => args.clone(),
            _ => Vec::new(),
        }
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
            // LR26: the scope ends here whichever way the branch goes, so what
            // it deferred runs once, before either.
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
            // LR10.3: a `repeat` condition reads what the body declared, so it
            // is lowered at the end of the body rather than in a block a
            // `continue` could jump to.
            self.gap(span, "`continue` inside `repeat`");
            return;
        };
        // LR26: leaving a loop leaves every scope inside it, so each one runs
        // what it deferred, innermost first.
        self.unwind_from(depth);
        self.jump_to(block, &carried);
    }

    /// LR25.3: `throw` does not complete. What it throws leaves every scope
    /// between here and whatever catches it.
    fn throw_stmt(&mut self, value: &Expr, span: Span) {
        let thrown = self.expr(value, Some(&Ty::Dynamic));
        self.raise(thrown, span);
    }

    /// Sends a thrown value to the innermost `try` around it, or out of the
    /// function where there is none (LR25.3).
    fn raise(&mut self, thrown: Value, span: Span) {
        let Some(handler) = self.handlers.last().cloned() else {
            if !self.throws {
                self.gap(span, "a throw the call graph did not reach");
                return;
            }
            // LR26: leaving the function leaves every scope it has open.
            self.unwind_from(0);
            let ty = self.function.result.clone();
            let returned = self.emit(
                InstKind::MakeEnum {
                    ty: ty.clone(),
                    variant: 1,
                    payload: vec![thrown],
                },
                ty,
                span,
            );
            self.terminate(Terminator::Return(returned));
            return;
        };

        self.unwind_from(handler.frame);
        let mut args = vec![thrown];
        args.extend(handler.carried.iter().map(|var| self.defs[var]));
        self.terminate(Terminator::Jump(Target::new(handler.block, args)));
    }

    /// LR25.3: the clauses are tried in the order they are written, the first
    /// whose type the thrown value has runs, and the `finally` runs whichever
    /// way the statement is left.
    fn try_stmt(
        &mut self,
        body: &Block,
        catches: &[CatchClause],
        finally: Option<&Block>,
        span: Span,
    ) {
        let carried = self.carried(body);
        let dispatch = self.function.add_block();
        let thrown = self.function.add_block_param(dispatch, Ty::Dynamic);
        self.add_params(dispatch, &carried);
        let entering = self.defs.clone();

        // The `finally` belongs to a scope around the guarded block, so it
        // runs after the handler rather than on the way to it.
        self.open();
        if let Some(finally) = finally {
            self.deferred
                .last_mut()
                .expect("a scope is open")
                .push(Cleanup::Finally(finally.clone()));
        }

        self.handlers.push(Handler {
            block: dispatch,
            frame: self.scopes.len(),
            carried: carried.clone(),
        });
        self.block(body);
        self.handlers.pop();

        let mut arrivals = Vec::new();
        if !self.left {
            arrivals.push(Arrival {
                block: self.current,
                defs: self.defs.clone(),
            });
        }

        self.switch_to(dispatch);
        self.defs = entering;
        self.bind_params(dispatch, &carried);
        for clause in catches {
            let next = self.function.add_block();
            let caught = match &clause.ty {
                Some(_) => {
                    let ty = self.recorded(clause.span);
                    let test = self.emit(
                        InstKind::IsType {
                            value: thrown,
                            ty: ty.clone(),
                        },
                        Ty::Bool,
                        clause.span,
                    );
                    let matched = self.function.add_block();
                    self.terminate(Terminator::Branch {
                        condition: test,
                        then: Target::to(matched),
                        otherwise: Target::to(next),
                    });
                    self.switch_to(matched);
                    self.emit(InstKind::DynValue { value: thrown }, ty, clause.span)
                }
                None => thrown,
            };

            let saved = self.defs.clone();
            self.open();
            let var = self.declare(&clause.name);
            self.defs.insert(var, caught);
            for stmt in &clause.body.stmts {
                if self.left {
                    break;
                }
                self.stmt(stmt);
            }
            self.close();
            if !self.left {
                arrivals.push(Arrival {
                    block: self.current,
                    defs: self.defs.clone(),
                });
            }

            self.defs = saved;
            self.switch_to(next);
            if clause.ty.is_none() {
                // Nothing after a clause that catches everything is reachable,
                // which the parser already rejected (LR0200).
                self.terminate(Terminator::Trap(Trap::Unreachable));
            }
        }

        // LR25.3: what no clause caught keeps going, once the `finally` around
        // the handler has run.
        if !self.left {
            self.raise(thrown, span);
        }

        let done = self.function.add_block();
        self.join(arrivals, done);
        self.close();
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
        // LR5.1: a declaration with a type takes it, and one without takes
        // what its initializer holds.
        let _ = ty;
        let declared = self.declared_type(span);

        match value {
            Some(value) => {
                let held = self.stored(value, declared.as_ref());
                self.bind_value(binding, held, span);
            }
            None => {
                // LR5.1: nothing has been written yet, and the checker proved
                // nothing reads it before something does.
                self.declare_binding(binding);
            }
        }
    }

    fn bind_value(&mut self, binding: &Binding, value: Value, span: Span) {
        match binding {
            Binding::Name(name) => {
                let var = self.declare(name);
                self.defs.insert(var, value);
                if self.context.facts.addressed(name) {
                    let slot = self.function.add_slot(self.function.type_of(value).clone());
                    self.slots.insert(var, slot);
                    self.emit_void(InstKind::SlotSet { slot, value }, span);
                }
            }
            Binding::Record(fields) => {
                let held = self.function.type_of(value).clone();
                let Some(declared) = self.fields_of(&held) else {
                    self.gap(span, "a record binding over a type with no fields");
                    self.declare_binding(binding);
                    return;
                };

                for written in fields {
                    let Some(index) = declared.iter().position(|(name, _)| name == &written.field)
                    else {
                        self.gap(
                            written.span,
                            "a record binding field the compiler could not find",
                        );
                        continue;
                    };
                    let field = u32::try_from(index).expect("field count fits in u32");
                    let field_value = self.emit(
                        InstKind::GetField {
                            object: value,
                            field,
                        },
                        declared[index].1.clone(),
                        written.span,
                    );
                    let name = written.bound_as.as_ref().unwrap_or(&written.field);
                    let var = self.declare(name);
                    self.defs.insert(var, field_value);
                }
            }
            Binding::Tuple(bindings) => {
                let Ty::Tuple(members) = self.function.type_of(value).clone() else {
                    self.gap(span, "a tuple binding over a value that is not a tuple");
                    self.declare_binding(binding);
                    return;
                };
                if bindings.len() != members.len() {
                    self.gap(span, "a tuple binding of another length");
                    self.declare_binding(binding);
                    return;
                }

                for (index, (binding, member)) in bindings.iter().zip(members).enumerate() {
                    let index = u32::try_from(index).expect("tuple length fits in u32");
                    let member = self.emit(
                        InstKind::GetElement {
                            tuple: value,
                            index,
                        },
                        member,
                        span,
                    );
                    self.bind_value(binding, member, span);
                }
            }
            Binding::Error => {}
        }
    }

    fn declare_binding(&mut self, binding: &Binding) {
        match binding {
            Binding::Name(name) => {
                self.declare(name);
            }
            Binding::Record(fields) => {
                for field in fields {
                    self.declare(field.bound_as.as_ref().unwrap_or(&field.field));
                }
            }
            Binding::Tuple(bindings) => {
                for binding in bindings {
                    self.declare_binding(binding);
                }
            }
            Binding::Error => {}
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

    /// LR55: an assignment evaluates its target before its value, and a
    /// compound assignment evaluates the target once.
    fn assign(&mut self, target: &Expr, op: Option<AstBinary>, value: &Expr, span: Span) {
        // LR55: reaching the method would read the target a second time, and
        // only a plain name can be read twice for nothing.
        if !matches!(target.kind, ExprKind::Name(_)) && self.overloading(op, target.span).is_some()
        {
            self.gap(
                span,
                "a compound assignment through a protocol on this target",
            );
            return;
        }

        match &target.kind {
            ExprKind::Name(name) => {
                let Some(var) = self.lookup(name) else {
                    self.gap(span, "an assignment to a name from another scope");
                    return;
                };
                let held = self.read_var(var, target.span);

                // LR5.4, LR36: `a += b` is `a = a:add(b)` where the operator
                // went through a protocol.
                let written = match self.overloading(op, target.span) {
                    Some((protocol, method, op)) => {
                        self.through_protocol(protocol, method, op, target, value, target.span)
                    }
                    None => self.written(held, op, value, span),
                };
                self.defs.insert(var, written);
                if let Some(slot) = self.slots.get(&var).copied() {
                    self.emit_void(
                        InstKind::SlotSet {
                            slot,
                            value: written,
                        },
                        span,
                    );
                }
            }

            // LR12.2, LR59: writing a field of a mutable struct.
            ExprKind::Field {
                receiver,
                name,
                optional: false,
            } => {
                let object = self.expr(receiver, None);
                let object = self.settled(object, span);
                let held = self.function.type_of(object).clone();

                // LR43: writing a property runs its setter, where it has one.
                if self.property(&held, name).is_some() {
                    self.write_property(object, &held, name, op, value, span);
                    return;
                }

                let (Some(index), Some(fields)) =
                    (self.field_index(&held, name), self.fields_of(&held))
                else {
                    self.gap(span, "an assignment to a member that is not a stored field");
                    return;
                };

                let ty = fields[index as usize].1.clone();
                let read = op.map(|_| {
                    self.emit(
                        InstKind::GetField {
                            object,
                            field: index,
                        },
                        ty.clone(),
                        span,
                    )
                });
                let written = self.written_into(read, &ty, op, value, span);
                self.emit_void(
                    InstKind::SetField {
                        object,
                        field: index,
                        value: written,
                    },
                    span,
                );
            }

            // LR37: writing an element of a container.
            ExprKind::Index {
                receiver,
                index,
                optional: false,
            } => {
                let container = self.expr(receiver, None);
                let container = self.settled(container, span);
                let held = self.function.type_of(container).clone();
                let Ty::Builtin { args, .. } = &held else {
                    self.gap(
                        span,
                        "an assignment into something the compiler cannot index",
                    );
                    return;
                };
                let (key, element) = match &held {
                    Ty::Builtin {
                        kind: Builtin::Map | Builtin::FrozenMap,
                        ..
                    } => (args.first().cloned(), args.get(1).cloned()),
                    _ => (Some(Ty::INT), args.first().cloned()),
                };
                let Some(element) = element else {
                    self.gap(span, "an assignment into a container with no element type");
                    return;
                };

                let index = self.expr(index, key.as_ref());
                let read = op.map(|_| {
                    self.emit(
                        InstKind::GetIndex {
                            receiver: container,
                            index,
                        },
                        element.clone(),
                        span,
                    )
                });
                let written = self.written_into(read, &element, op, value, span);
                self.emit_void(
                    InstKind::SetIndex {
                        receiver: container,
                        index,
                        value: written,
                    },
                    span,
                );
            }

            _ => self.gap(span, "an assignment to this target"),
        }
    }

    /// LR43: writing a property runs its setter. A compound assignment reads
    /// through the getter first, which is the same target evaluated once
    /// (LR5.4, LR55).
    fn write_property(
        &mut self,
        object: Value,
        held: &Ty,
        name: &str,
        op: Option<AstBinary>,
        value: &Expr,
        span: Span,
    ) {
        let Some((get, ty)) = self.getter(held, name) else {
            self.gap(span, "a property the compiler could not read");
            return;
        };
        let Some(set) = self.property(held, name).and_then(|held| held.set) else {
            self.gap(span, "an assignment to a property with no setter");
            return;
        };

        let read = op.map(|_| {
            self.emit(
                InstKind::Call {
                    callee: get,
                    type_args: Vec::new(),
                    args: vec![object],
                },
                ty.clone(),
                span,
            )
        });
        let written = self.written_into(read, &ty, op, value, span);
        self.emit_void(
            InstKind::Call {
                callee: set,
                type_args: Vec::new(),
                args: vec![object, written],
            },
            span,
        );
    }

    /// What an assignment writes: the value, or what the operator makes of
    /// what the target already held and the value (LR5.4).
    fn written(&mut self, held: Value, op: Option<AstBinary>, value: &Expr, span: Span) -> Value {
        let wanted = self.function.type_of(held).clone();
        self.written_into(Some(held), &wanted, op, value, span)
    }

    /// The protocol an operator went through, where the checker sent it to one
    /// (LR36).
    fn overloading(
        &self,
        op: Option<AstBinary>,
        at: Span,
    ) -> Option<(&'static str, &'static str, AstBinary)> {
        let op = op?;
        self.context.facts.call(at)?;
        let (_, protocol, method) = protocol_of(op)?;
        Some((protocol, method, op))
    }

    fn written_into(
        &mut self,
        held: Option<Value>,
        wanted: &Ty,
        op: Option<AstBinary>,
        value: &Expr,
        span: Span,
    ) -> Value {
        let right = self.stored(value, Some(wanted));
        let (Some(left), Some(op)) = (held, op) else {
            return right;
        };
        match binary_op(op) {
            Some(op) => self.emit(InstKind::Binary { op, left, right }, wanted.clone(), span),
            None => self.missing(span, "a compound assignment with this operator"),
        }
    }

    fn ret(&mut self, value: Option<&Expr>, span: Span) {
        let result = self.declared.clone();
        let value = match value {
            Some(expr) => self.stored(expr, Some(&result)),
            None => self.emit(InstKind::Const(Const::Unit), Ty::Unit, span),
        };
        // LR26: a `return` leaves every scope the function has open, so
        // everything they deferred runs, innermost first.
        self.unwind_from(0);
        let returned = self.returned(value, span);
        self.terminate(Terminator::Return(returned));
    }

    /// What `Return` gives back for a value the function returned. Where an
    /// exception can escape, that is one half of what it gives back (LR25.3).
    fn returned(&mut self, value: Value, span: Span) -> Value {
        if !self.throws {
            return value;
        }
        let ty = self.function.result.clone();
        self.emit(
            InstKind::MakeEnum {
                ty: ty.clone(),
                variant: 0,
                payload: vec![value],
            },
            ty,
            span,
        )
    }

    // -- expressions ------------------------------------------------------

    /// Lowers `expr`, and gives back the value it produces.
    /// LR31: a struct is copied when it reaches a new holder, so a mutation
    /// through one is not observable through another. A value just built has
    /// no other holder, so only one read out of a place is copied.
    fn stored(&mut self, expr: &Expr, wanted: Option<&Ty>) -> Value {
        let value = self.expr(expr, wanted);
        if !matches!(
            expr.kind,
            ExprKind::Name(_) | ExprKind::Field { .. } | ExprKind::Index { .. }
        ) {
            return value;
        }

        let ty = self.function.type_of(value).clone();
        if !self.is_value_struct(&ty) {
            return value;
        }
        self.emit(InstKind::CopyValue { value }, ty, expr.span)
    }

    /// Whether `ty` is a struct with value semantics. A `ref struct` is one
    /// object every holder observes, so it is never copied (LR31).
    fn is_value_struct(&self, ty: &Ty) -> bool {
        let Ty::Named { id, .. } = ty else {
            return false;
        };
        match &self.context.program.nominal(*id).shape {
            Shape::Struct(structure) => !structure.reference,
            _ => false,
        }
    }

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
                Some(var) => {
                    let value = self.read_var(var, span);
                    // LR57: a name the checker proved holds something reads
                    // as what it holds.
                    if let Ty::Optional(inner) = self.function.type_of(value).clone()
                        && self.maybe_recorded(span).as_ref() == Some(inner.as_ref())
                    {
                        return self.emit(InstKind::Unwrap { value }, *inner, span);
                    }
                    value
                }
                None => self.constant(name, wanted, span),
            },

            // LR36: a unary operator the checker sent through a protocol is a
            // call to the method it named, taking nothing beside the receiver.
            ExprKind::Unary { op, operand }
                if self.context.facts.call(operand.span).is_some()
                    && matches!(op, AstUnary::Negate | AstUnary::BitNot) =>
            {
                let method = match op {
                    AstUnary::BitNot => "bitNot",
                    _ => "neg",
                };
                self.call(operand, Some(method), &[], operand.span)
            }

            ExprKind::Unary { op, operand } => {
                let ty = match op {
                    AstUnary::Not => Ty::Bool,
                    _ => wanted.cloned().unwrap_or_else(|| self.recorded(span)),
                };
                let operand = self.expr(operand, Some(&ty));
                let op = match op {
                    AstUnary::Not => UnaryOp::Not,
                    AstUnary::Negate => UnaryOp::Negate,
                    AstUnary::BitNot => UnaryOp::BitNot,
                };
                self.emit(InstKind::Unary { op, operand }, ty, span)
            }

            ExprKind::Binary {
                op,
                op_span,
                left,
                right,
            } => self.binary(*op, *op_span, left, right, span),

            ExprKind::Call {
                callee,
                method,
                args,
                ..
            } => self.call(callee, method.as_deref(), args, span),

            ExprKind::Record { path, fields } => self.record(path, fields, wanted, span),
            ExprKind::Function {
                asynchronous,
                params,
                body,
                ..
            } => {
                if *asynchronous {
                    return self.missing(span, "an async closure");
                }
                self.closure(params, body, span)
            }
            ExprKind::List(values) => self.list(values, wanted, span),
            ExprKind::Map(entries) => self.map(entries, wanted, span),
            ExprKind::Set(values) => self.set(values, wanted, span),
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

            ExprKind::Try(inner) => self.propagate(inner, span),
            ExprKind::Await(_) => self.missing(span, "await"),

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

            // LR72: a binding whose address is taken lives in a slot, and
            // `&x` is that slot's address.
            ExprKind::AddressOf { mutable, operand } => match &operand.kind {
                ExprKind::Name(name) => {
                    let slot = self
                        .lookup(name)
                        .and_then(|var| self.slots.get(&var).copied());
                    let Some(slot) = slot else {
                        return self.missing(span, "an address of a binding a pattern bound");
                    };
                    let ty = self.recorded(span);
                    self.emit(
                        InstKind::AddressOf {
                            mutable: *mutable,
                            slot,
                        },
                        ty,
                        span,
                    )
                }
                ExprKind::Field {
                    receiver,
                    name,
                    optional: false,
                } => {
                    let object = self.expr(receiver, None);
                    let object = self.settled(object, operand.span);
                    let held = self.function.type_of(object).clone();
                    let Some(field) = self.field_index(&held, name) else {
                        return self
                            .missing(span, "an address of a member that is not a stored field");
                    };
                    let ty = self.recorded(span);
                    self.emit(
                        InstKind::FieldAddress {
                            mutable: *mutable,
                            object,
                            field,
                        },
                        ty,
                        span,
                    )
                }
                _ => self.missing(span, "an address of an element"),
            },

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

    fn propagate(&mut self, inner: &Expr, span: Span) -> Value {
        let result = self.expr(inner, None);
        let Ty::Builtin {
            kind: Builtin::Result,
            args,
        } = self.function.type_of(result).clone()
        else {
            return self.missing(span, "`?` on a value that is not a `Result`");
        };
        let (Some(value_ty), Some(error_ty)) = (args.first().cloned(), args.get(1).cloned()) else {
            return self.missing(span, "a `Result` without both type arguments");
        };

        let returned = self.declared.clone();
        let Ty::Builtin {
            kind: Builtin::Result,
            args: returned_args,
        } = &returned
        else {
            return self.missing(span, "`?` in a function that does not return `Result`");
        };
        let Some(returned_error) = returned_args.get(1).cloned() else {
            return self.missing(span, "a returned `Result` without an error type");
        };

        let failed = self.function.add_block();
        let succeeded = self.function.add_block();
        let tag = self.emit(InstKind::GetTag { value: result }, Ty::INT, span);
        let err = self.emit(InstKind::Const(Const::Int(1)), Ty::INT, span);
        let is_err = self.emit(
            InstKind::Binary {
                op: BinaryOp::Equal,
                left: tag,
                right: err,
            },
            Ty::Bool,
            span,
        );
        self.terminate(Terminator::Branch {
            condition: is_err,
            then: Target::to(failed),
            otherwise: Target::to(succeeded),
        });

        self.switch_to(failed);
        let error = self.emit(
            InstKind::GetPayload {
                value: result,
                variant: 1,
                field: 0,
            },
            error_ty,
            span,
        );
        let error = self.propagated_error(error, &returned_error, span);
        let returned = self.emit(
            InstKind::MakeEnum {
                ty: returned.clone(),
                variant: 1,
                payload: vec![error],
            },
            returned,
            span,
        );
        self.unwind_from(0);
        let returned = self.returned(returned, span);
        self.terminate(Terminator::Return(returned));

        self.switch_to(succeeded);
        self.emit(
            InstKind::GetPayload {
                value: result,
                variant: 0,
                field: 0,
            },
            value_ty,
            span,
        )
    }

    fn propagated_error(&mut self, error: Value, wanted: &Ty, span: Span) -> Value {
        if self.function.type_of(error) == wanted {
            return error;
        }

        let Some(declaration) = self.context.facts.call(span) else {
            return self.missing(
                span,
                "a propagated error conversion the checker did not resolve",
            );
        };
        if let Some(method) = self.context.virtuals.get(&declaration).copied() {
            return self.emit(
                InstKind::CallVirtual {
                    method,
                    receiver: error,
                    args: Vec::new(),
                },
                wanted.clone(),
                span,
            );
        }

        let Some(reached) = self.context.callees.get(&declaration) else {
            return self.missing(span, "a propagated error conversion with no body");
        };
        if !reached.takes_self || !reached.params.is_empty() {
            return self.missing(span, "an invalid propagated error conversion");
        }
        let type_args = if reached.type_params.is_empty() {
            Vec::new()
        } else {
            let Some(type_args) = self.type_args(span, reached.type_params.len()) else {
                return self.missing(
                    span,
                    "a propagated error conversion with unknown type arguments",
                );
            };
            type_args
        };

        self.emit(
            InstKind::Call {
                callee: reached.id,
                type_args,
                args: vec![error],
            },
            wanted.clone(),
            span,
        )
    }

    fn binary(
        &mut self,
        op: AstBinary,
        op_span: Span,
        left: &Expr,
        right: &Expr,
        span: Span,
    ) -> Value {
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

        // LR36: an operator the checker sent through a protocol is the call it
        // named, and nothing else here applies to it.
        if self.context.facts.call(op_span).is_some()
            && let Some((_, protocol, method)) = protocol_of(op)
        {
            return self.through_protocol(protocol, method, op, left, right, op_span);
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

    /// LR36: `a + b` is `a:add(b)`, and the four ordering operators are one
    /// `compare` against zero, which is what keeps them consistent.
    fn through_protocol(
        &mut self,
        protocol: &str,
        method: &str,
        op: AstBinary,
        left: &Expr,
        right: &Expr,
        span: Span,
    ) -> Value {
        let args = vec![Argument {
            name: None,
            value: right.clone(),
            span: right.span,
        }];
        let called = self.call(left, Some(method), &args, span);

        match (protocol, op) {
            ("Eq", AstBinary::NotEqual) => self.emit(
                InstKind::Unary {
                    op: UnaryOp::Not,
                    operand: called,
                },
                Ty::Bool,
                span,
            ),
            ("Comparable", _) => {
                let Some(op) = binary_op(op) else {
                    return self.missing(span, "an ordering operator");
                };
                let zero = self.emit(InstKind::Const(Const::Int(0)), Ty::Int(IntTy::I64), span);
                self.emit(
                    InstKind::Binary {
                        op,
                        left: called,
                        right: zero,
                    },
                    Ty::Bool,
                    span,
                )
            }
            _ => called,
        }
    }

    /// LR9.1: a call passes an argument for every parameter, at the type that
    /// parameter takes.
    fn memory_method(
        &mut self,
        callee: &Expr,
        name: &str,
        target: Ty,
        args: &[Argument],
        span: Span,
    ) -> Value {
        let pointer = self.expr(callee, None);
        match (name, args) {
            ("read", []) => self.emit(InstKind::Load { pointer }, target, span),
            ("write", [argument]) => {
                let value = self.stored(&argument.value, Some(&target));
                self.emit_void(InstKind::Store { pointer, value }, span);
                self.emit(InstKind::Const(Const::Unit), Ty::Unit, span)
            }
            ("add", [argument]) => {
                let count = self.expr(&argument.value, Some(&Ty::Int(IntTy::Isize)));
                let ty = self.function.type_of(pointer).clone();
                self.emit(InstKind::Offset { pointer, count }, ty, span)
            }
            _ => self.missing(span, "a memory method of this shape"),
        }
    }

    fn call(
        &mut self,
        callee: &Expr,
        method: Option<&str>,
        args: &[Argument],
        span: Span,
    ) -> Value {
        if self.context.facts.freezes(span) {
            let value = self.expr(callee, None);
            let ty = self.recorded(span);
            return self.emit(InstKind::Freeze { value }, ty, span);
        }
        if self.context.facts.checked_index(span) {
            return self.checked_index(callee, args, span);
        }
        if self.context.facts.contains(span) {
            return self.contains(callee, args, span);
        }
        if let Some(mutation) = self.context.facts.collection_mutation(span) {
            return self.collection_mutation(mutation, callee, args, span);
        }
        if let Some(method) = self.context.facts.overflow_method(span) {
            return self.overflow_method(method, callee, args, span);
        }

        if let Some(intrinsic) = self.context.facts.intrinsic(span) {
            return self.intrinsic(intrinsic, args, span);
        }

        if let ExprKind::Field {
            receiver,
            name: variant,
            ..
        } = &callee.kind
            && let ExprKind::Name(written) = &receiver.kind
            && written == "Result"
            && self.lookup(written).is_none()
            && let Some(tag) = match variant.as_str() {
                "Ok" => Some(0),
                "Err" => Some(1),
                _ => None,
            }
        {
            let ty = self.recorded(span);
            if matches!(
                ty,
                Ty::Builtin {
                    kind: Builtin::Result,
                    ..
                }
            ) {
                return self.construct(ty, tag, args, span);
            }
        }

        // LR15.3: a variant with a payload is written like a call and builds a
        // value, so it reaches no function and the checker recorded none.
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

        // LR9.2: a name holding a function value is called through the value,
        // and reaches no declaration.
        if method.is_none()
            && self
                .known_type(callee)
                .is_some_and(|ty| matches!(ty, Ty::Function { .. }))
        {
            return self.through(callee, args, span);
        }

        // LR72: a raw pointer's methods reach no declaration; `read` and
        // `write` are the load and the store themselves.
        if let Some(name) = method
            && let Some(Ty::Pointer { target, .. }) = self.known_type(callee)
        {
            return self.memory_method(callee, name, *target, args, span);
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

        // LR27: the call produces a `Task`, which is what the state machine
        // this function has not been turned into would build.
        if reached.asynchronous {
            return self.missing(span, "a call to an async function");
        }

        if reached.params.iter().any(|param| param.variadic) {
            return self.missing(span, "a call to a variadic function");
        }

        // LR19: a generic call carries what fills each of the callee's type
        // parameters, which is what monomorphization substitutes.
        let declared = reached.type_params.clone();
        let type_args = if declared.is_empty() {
            Vec::new()
        } else {
            match self.type_args(span, declared.len()) {
                Some(args) => args,
                // A method of a generic type takes the type's parameters as
                // well as its own, and the checker works out only its own.
                None => return self.missing(span, "a call whose type arguments are not all known"),
            }
        };

        let id = reached.id;
        let takes_self = reached.takes_self;
        // The caller is not inside the callee's type parameters, so it passes
        // its arguments at the parameter types with those already filled in.
        let wanted: Vec<Ty> = reached
            .params
            .iter()
            .map(|param| param.ty.substitute(&declared, &type_args))
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
            let value = self.stored(&argument.value, slot.map(|slot| &wanted[slot]));
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
            filled[slot] = Some(self.stored(default, Some(&wanted[slot])));
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
        if reached.throws {
            let produced = self.emit(
                InstKind::Call {
                    callee: id,
                    type_args,
                    args: passed,
                },
                thrown_or(result.clone()),
                span,
            );
            return self.caught_or_raised(produced, result, span);
        }

        self.emit(
            InstKind::Call {
                callee: id,
                type_args,
                args: passed,
            },
            result,
            span,
        )
    }

    fn intrinsic(&mut self, intrinsic: Intrinsic, args: &[Argument], span: Span) -> Value {
        let constructed = self.recorded(span);
        match (&intrinsic, &constructed) {
            (
                Intrinsic::ListNew,
                Ty::Builtin {
                    kind: Builtin::List,
                    args,
                },
            ) => {
                let Some(element) = args.first().cloned() else {
                    return self.missing(span, "a list constructor without an element type");
                };
                return self.emit(
                    InstKind::MakeList {
                        element,
                        values: Vec::new(),
                    },
                    constructed,
                    span,
                );
            }
            (
                Intrinsic::MapNew,
                Ty::Builtin {
                    kind: Builtin::Map,
                    args,
                },
            ) => {
                let (Some(key), Some(value)) = (args.first().cloned(), args.get(1).cloned()) else {
                    return self.missing(span, "a map constructor without key and value types");
                };
                return self.emit(
                    InstKind::MakeMap {
                        key,
                        value,
                        entries: Vec::new(),
                    },
                    constructed,
                    span,
                );
            }
            (
                Intrinsic::SetNew,
                Ty::Builtin {
                    kind: Builtin::Set,
                    args,
                },
            ) => {
                let Some(element) = args.first().cloned() else {
                    return self.missing(span, "a set constructor without an element type");
                };
                return self.emit(
                    InstKind::MakeSet {
                        element,
                        values: Vec::new(),
                    },
                    constructed,
                    span,
                );
            }
            (Intrinsic::ListNew | Intrinsic::MapNew | Intrinsic::SetNew, _) => {
                return self.missing(span, "a collection constructor with an unresolved type");
            }
            _ => {}
        }

        if intrinsic == Intrinsic::DebugAssert && self.context.mode == CompilationMode::Release {
            return self.emit(InstKind::Const(Const::Unit), Ty::Unit, span);
        }

        if intrinsic == Intrinsic::Panic {
            let message = args
                .first()
                .map(|argument| self.expr(&argument.value, Some(&Ty::Str)))
                .unwrap_or_else(|| self.missing(span, "a panic message"));
            return self.emit(InstKind::Panic { message }, Ty::Never, span);
        }

        let mut condition = None;
        let mut message = None;
        let mut position = 0;
        for argument in args {
            let slot = match argument.name.as_deref() {
                Some("condition") => 0,
                Some("message") => 1,
                _ => {
                    let slot = position;
                    position += 1;
                    slot
                }
            };
            let wanted = if slot == 0 { Ty::Bool } else { Ty::Str };
            let value = self.expr(&argument.value, Some(&wanted));
            if slot == 0 {
                condition = Some(value);
            } else {
                message = Some(value);
            }
        }

        let condition = condition.unwrap_or_else(|| self.missing(span, "an assertion condition"));
        self.emit_void(InstKind::Assert { condition, message }, span);
        self.emit(InstKind::Const(Const::Unit), Ty::Unit, span)
    }

    fn checked_index(&mut self, callee: &Expr, args: &[Argument], span: Span) -> Value {
        let receiver = self.expr(callee, None);
        let held = self.function.type_of(receiver).clone();
        let Ty::Builtin {
            kind,
            args: type_args,
        } = &held
        else {
            return self.missing(
                span,
                "a checked lookup on something that is not a collection",
            );
        };
        let wanted = match kind {
            Builtin::Map | Builtin::FrozenMap => type_args.first().cloned(),
            Builtin::List | Builtin::FrozenList => Some(Ty::INT),
            _ => None,
        };
        let (Some(wanted), [argument]) = (wanted, args) else {
            return self.missing(span, "a checked lookup without one key");
        };
        let index = self.expr(&argument.value, Some(&wanted));
        let result = self.recorded(span);
        self.emit(InstKind::GetCheckedIndex { receiver, index }, result, span)
    }

    fn collection_mutation(
        &mut self,
        mutation: CollectionMutation,
        callee: &Expr,
        args: &[Argument],
        span: Span,
    ) -> Value {
        let receiver = self.expr(callee, None);
        let Some(element) = self.collection_args(receiver).first().cloned() else {
            return self.missing(span, "a collection mutation without an element type");
        };
        let kind = match mutation {
            CollectionMutation::ListPop => {
                let result = self.recorded(span);
                return self.emit(InstKind::ListPop { receiver }, result, span);
            }
            CollectionMutation::Clear => return self.missing(span, "a clear"),
            CollectionMutation::MapRemove | CollectionMutation::SetRemove => {
                let Some(argument) = args.first() else {
                    return self.missing(span, "a removal without a key");
                };
                let key = self.expr(&argument.value, Some(&element));
                let result = self.recorded(span);
                let kind = match mutation {
                    CollectionMutation::MapRemove => InstKind::MapRemove { receiver, key },
                    _ => InstKind::SetRemove {
                        receiver,
                        value: key,
                    },
                };
                return self.emit(kind, result, span);
            }
            CollectionMutation::ListPush | CollectionMutation::SetInsert => {
                let Some(argument) = args.first() else {
                    return self.missing(span, "a collection mutation without a value");
                };
                let value = self.expr(&argument.value, Some(&element));
                match mutation {
                    CollectionMutation::ListPush => InstKind::ListPush { receiver, value },
                    _ => InstKind::SetInsert { receiver, value },
                }
            }
        };
        self.emit_void(kind, span);
        self.emit(InstKind::Const(Const::Unit), Ty::Unit, span)
    }

    fn contains(&mut self, callee: &Expr, args: &[Argument], span: Span) -> Value {
        let receiver = self.expr(callee, None);
        let Some(element) = self.collection_args(receiver).first().cloned() else {
            return self.missing(span, "a lookup without a key type");
        };
        let Some(argument) = args.first() else {
            return self.missing(span, "a lookup without a key");
        };
        let value = self.expr(&argument.value, Some(&element));
        self.emit(InstKind::Contains { receiver, value }, Ty::Bool, span)
    }

    /// LR4.3: `x:wrappingAdd(y)` and its kin apply the operator they name
    /// with the overflow behavior they name.
    fn overflow_method(
        &mut self,
        method: OverflowMethod,
        callee: &Expr,
        args: &[Argument],
        span: Span,
    ) -> Value {
        let Some(op) = binary_op(method.op) else {
            return self.missing(span, "an overflow-explicit operator");
        };
        let result = self.recorded(span);
        let operand = match &result {
            Ty::Optional(inner) => inner.as_ref().clone(),
            other => other.clone(),
        };
        let left = self.expr(callee, Some(&operand));
        let Some(argument) = args.first() else {
            return self.missing(span, "an overflow-explicit operation without an operand");
        };
        let right = self.expr(&argument.value, Some(&operand));
        let mode = match method.mode {
            luar_sema::facts::Overflow::Wrap => Overflow::Wrap,
            luar_sema::facts::Overflow::Saturate => Overflow::Saturate,
            luar_sema::facts::Overflow::Check => Overflow::Check,
        };
        self.emit(
            InstKind::Overflowing {
                mode,
                op,
                left,
                right,
            },
            result,
            span,
        )
    }

    /// LR25.3: a call that may have thrown says which happened, so the caller
    /// reads what it returned on one path and sends what it threw on outward
    /// on the other.
    fn caught_or_raised(&mut self, produced: Value, result: Ty, span: Span) -> Value {
        let tag = self.emit(InstKind::GetTag { value: produced }, Ty::INT, span);
        let threw = self.emit(InstKind::Const(Const::Int(1)), Ty::INT, span);
        let raised = self.emit(
            InstKind::Binary {
                op: BinaryOp::Equal,
                left: tag,
                right: threw,
            },
            Ty::Bool,
            span,
        );

        let unwinding = self.function.add_block();
        let returned = self.function.add_block();
        self.terminate(Terminator::Branch {
            condition: raised,
            then: Target::to(unwinding),
            otherwise: Target::to(returned),
        });

        self.switch_to(unwinding);
        let thrown = self.emit(
            InstKind::GetPayload {
                value: produced,
                variant: 1,
                field: 0,
            },
            Ty::Dynamic,
            span,
        );
        self.raise(thrown, span);

        self.switch_to(returned);
        self.emit(
            InstKind::GetPayload {
                value: produced,
                variant: 0,
                field: 0,
            },
            result,
            span,
        )
    }

    /// What fills the callee's type parameters at `span`, where the checker
    /// worked out every one of them (LR19).
    fn type_args(&mut self, span: Span, wanted: usize) -> Option<Vec<Ty>> {
        let recorded = self.context.facts.type_args(span)?;
        if recorded.len() != wanted {
            return None;
        }
        recorded
            .iter()
            .map(|ty| types::convert(ty, self.context.ids).ok())
            .collect()
    }

    /// LR12.1, LR12.2: a literal gives a value for every field, and a field
    /// with a default may be left out.
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
            let value = self.stored(&init.value, slot.map(|slot| &declared[slot].1));
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
                Some(default) => self.stored(&default, Some(held)),
                // LR12.1: a field a record leaves out is one nothing was given
                // for, which only an optional field may be.
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

            // LR43: a property reads like a field and runs code, so a read of
            // one is a call to its getter.
            if let Some((get, ty)) = self.getter(&held, name) {
                return self.emit(
                    InstKind::Call {
                        callee: get,
                        type_args: Vec::new(),
                        args: vec![object],
                    },
                    ty,
                    span,
                );
            }

            // LR13: `length` is read off the collection's header.
            if name == "length"
                && matches!(
                    held,
                    Ty::Builtin {
                        kind: Builtin::List
                            | Builtin::FrozenList
                            | Builtin::Map
                            | Builtin::FrozenMap
                            | Builtin::Set
                            | Builtin::FrozenSet,
                        ..
                    }
                )
            {
                return self.emit(InstKind::Length { receiver: object }, Ty::INT, span);
            }

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
            .map(|(argument, held)| self.stored(&argument.value, Some(held)))
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

    /// LR9.2, LR9.8: a closure is a function of the program, plus the values
    /// it captured from the scope it was written in.
    fn closure(&mut self, params: &[Param], body: &FunctionBody, span: Span) -> Value {
        let ty = self.recorded(span);
        let Ty::Function {
            params: takes,
            result,
        } = ty.clone()
        else {
            return self.missing(span, "a closure whose type the checker did not work out");
        };
        if takes.len() != params.len() {
            return self.missing(span, "a closure of a shape the checker did not agree on");
        }
        // LR25.3: a function type says nothing about throwing, so a closure
        // that throws has nowhere to say it does.
        if throws::closure_escapes(body, self.context.throwing, self.context.facts) {
            return self.missing(span, "a throw inside a closure");
        }

        let written = match body {
            FunctionBody::Block(block) => block.clone(),
            // An arrow closure is one expression, and returning it is what it
            // does (LR9.2).
            FunctionBody::Expr(value) => Block {
                stmts: vec![Stmt::new(StmtKind::Return(Some(value.clone())), value.span)],
                span: value.span,
            },
        };

        let Some(captures) = self.captures(&written, span) else {
            return self.missing(span, "a closure capturing a binding something assigns to");
        };
        if captures.iter().any(|(_, var)| self.slots.contains_key(var)) {
            return self.missing(span, "a closure capturing a binding whose address is taken");
        }

        let captured: Vec<(String, Ty)> = captures
            .iter()
            .map(|(name, var)| (name.clone(), self.function.type_of(self.defs[var]).clone()))
            .collect();
        let mut bindings: Vec<Binding> = Vec::with_capacity(params.len());
        let mut taken: Vec<Ty> = vec![ty.clone()];
        for (param, ty) in params.iter().zip(takes) {
            bindings.push(param.binding.clone());
            taken.push(ty);
        }

        let id = FuncId(self.context.next_function.get());
        self.context.next_function.set(id.0 + 1);

        let shell = Function::new(
            format!("{}#{}", self.function.name, id.0),
            taken,
            *result,
            span,
        );
        let (built, made, gaps) =
            Body::new(self.context, shell, false).lower(Some(&captured), &bindings, &written);
        self.made.push((id, built));
        self.made.extend(made);
        self.gaps.extend(gaps);

        let held = captures.iter().map(|(_, var)| self.defs[var]).collect();
        self.emit(
            InstKind::MakeClosure {
                func: id,
                captures: held,
            },
            ty,
            span,
        )
    }

    /// The bindings a closure body reaches out of its own scope for, in the
    /// order it names them.
    fn captures(&mut self, body: &Block, span: Span) -> Option<Vec<(String, Var)>> {
        let _ = span;
        let mut inside = Vec::new();
        assigned(body, &mut inside);

        let mut named = Vec::new();
        names::in_block(body, &mut named);

        let mut captures: Vec<(String, Var)> = Vec::new();
        for name in named {
            let Some(var) = self.lookup(&name) else {
                continue;
            };
            if !self.defs.contains_key(&var) || captures.iter().any(|(_, held)| *held == var) {
                continue;
            }
            if self.mutated.contains(&name) || inside.contains(&name) {
                return None;
            }
            captures.push((name, var));
        }
        Some(captures)
    }

    /// LR9.2: a call through a value calls whatever it holds, which is a
    /// closure or a function passed as one.
    fn through(&mut self, callee: &Expr, args: &[Argument], span: Span) -> Value {
        let value = self.expr(callee, None);
        let Ty::Function { params, result } = self.function.type_of(value).clone() else {
            return self.missing(span, "a call through something that is not a function");
        };
        if args.len() != params.len() || args.iter().any(|argument| argument.name.is_some()) {
            return self.missing(span, "a call through a value that does not line up");
        }

        let passed = args
            .iter()
            .zip(&params)
            .map(|(argument, ty)| self.stored(&argument.value, Some(ty)))
            .collect();
        // LR9.3: what a call through a function value gives back is what the
        // function type says, which is more than the checker settles today.
        let held = self.maybe_recorded(span).unwrap_or(*result);
        self.emit(
            InstKind::CallIndirect {
                callee: value,
                args: passed,
            },
            held,
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

    /// LR13.3: `Set { ... }` builds a set.
    fn set(&mut self, values: &[Expr], wanted: Option<&Ty>, span: Span) -> Value {
        let ty = self.settled_type(wanted, span);
        let Ty::Builtin { args, .. } = &ty else {
            return self.missing(span, "a set literal whose elements have no type");
        };
        let Some(element) = args.first().cloned() else {
            return self.missing(span, "a set literal whose elements have no type");
        };
        let values = values
            .iter()
            .map(|value| self.expr(value, Some(&element)))
            .collect();
        self.emit(InstKind::MakeSet { element, values }, ty, span)
    }

    /// LR37: `x[i]` reads what the container holds at `i`. LR69: a map hands
    /// back an optional, because a key it does not hold is not a mistake.
    fn index(&mut self, receiver: &Expr, index: &Expr, optional: bool, span: Span) -> Value {
        if optional {
            return self.missing(span, "an optional index");
        }

        // LR55: the container is written before the index, so it is evaluated
        // first.
        // LR36: a type the checker sent through `Index` reads through the
        // method it named.
        if self.context.facts.call(span).is_some() {
            let args = vec![Argument {
                name: None,
                value: index.clone(),
                span: index.span,
            }];
            return self.call(receiver, Some("index"), &args, span);
        }

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
            _ => Some(Ty::INT),
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

    /// What a variant carries, in the order the enum declares it (LR15.2),
    /// with the arguments the type carries where its parameters were (LR19).
    fn payload_of(&self, ty: &Ty, variant: u32) -> Option<Vec<Ty>> {
        if let Ty::Builtin {
            kind: Builtin::Result,
            args,
        } = ty
        {
            return args.get(variant as usize).cloned().map(|ty| vec![ty]);
        }

        let Ty::Named { id, args } = ty else {
            return None;
        };
        let nominal = self.context.program.nominal(*id);
        let Shape::Enum(enumeration) = &nominal.shape else {
            return None;
        };
        let held = enumeration.variants.get(variant as usize)?;
        Some(
            held.fields
                .iter()
                .map(|field| field.ty.substitute(&nominal.type_params, args))
                .collect(),
        )
    }

    /// The fields a type stores, in the order it declares them.
    fn fields_of(&self, ty: &Ty) -> Option<Vec<(String, Ty)>> {
        match ty {
            Ty::Named { id, args } => {
                let nominal = self.context.program.nominal(*id);
                let Shape::Struct(structure) = &nominal.shape else {
                    return None;
                };
                Some(
                    structure
                        .fields
                        .iter()
                        .map(|field| {
                            (
                                field.name.clone(),
                                field.ty.substitute(&nominal.type_params, args),
                            )
                        })
                        .collect(),
                )
            }
            Ty::Record(fields) => Some(fields.clone()),
            _ => None,
        }
    }

    /// The property `name` names on `ty`, if it names one (LR43).
    fn property(&self, ty: &Ty, name: &str) -> Option<&Property> {
        let Ty::Named { id, .. } = ty else {
            return None;
        };
        self.context.properties.get(&(*id, name.to_owned()))
    }

    /// The function a read of `name` goes through, and what it gives back.
    fn getter(&self, ty: &Ty, name: &str) -> Option<(FuncId, Ty)> {
        let Ty::Named { args, .. } = ty else {
            return None;
        };
        let held = self.property(ty, name)?;
        // LR19: a property of `Box<int>` gives back what `T` is filled with.
        let params = self.owner_params(ty)?;
        Some((held.get, held.ty.substitute(&params, args)))
    }

    fn owner_params(&self, ty: &Ty) -> Option<Vec<String>> {
        let Ty::Named { id, .. } = ty else {
            return None;
        };
        Some(self.context.program.nominal(*id).type_params.clone())
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
            .map(|argument| self.stored(&argument.value, None))
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
    fn coerce(&mut self, value: Value, wanted: &Ty, span: Span) -> Value {
        let held = self.function.type_of(value).clone();
        match wanted {
            Ty::Optional(inner) if held == **inner => {
                self.emit(InstKind::MakeSome { value }, wanted.clone(), span)
            }
            // LR6.3, LR25.3: what a value is is not written down, so it
            // carries it.
            Ty::Dynamic if held != Ty::Dynamic => self.emit(
                InstKind::MakeDyn {
                    interface: None,
                    value,
                },
                Ty::Dynamic,
                span,
            ),
            // LR18.1: a value used through an interface carries which
            // implementation to dispatch to.
            _ if held != *wanted => match self.interface_id(wanted) {
                Some(interface) => self.emit(
                    InstKind::MakeDyn {
                        interface: Some(interface),
                        value,
                    },
                    wanted.clone(),
                    span,
                ),
                None => value,
            },
            _ => value,
        }
    }

    /// The interface `ty` names, if it names one.
    fn interface_id(&self, ty: &Ty) -> Option<TypeId> {
        let Ty::Named { id, .. } = ty else {
            return None;
        };
        matches!(self.context.program.nominal(*id).shape, Shape::Interface(_)).then_some(*id)
    }
}

/// The names `block` assigns to, anywhere inside it.
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
