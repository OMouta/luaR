//! Lowering one function body.

mod builtins;
mod calls;
mod construct;
mod expr;
mod iterate;
mod patterns;
mod stmt;

use std::cell::Cell;
use std::collections::{HashMap, HashSet};

use luar_ast::{Binding, Block, Expr, ExprKind};
use luar_diagnostics::Span;
use luar_sema::facts::Facts;
use luar_sema::modules::ModuleId;

use luar_sema::types::Type;

use crate::inst::MethodId;
use crate::inst::{Const, Inst, InstKind, Target, Terminator, Trap, Value};
use crate::lower::types::{self, Ids};
use crate::lower::{Callee, CompilationMode, Gap, Property};
use crate::program::{BlockId, FuncId, Function, Program, SlotId};
use crate::ty::{Builtin, Ty, TypeId};
use stmt::assigned;

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

    // -- control flow -----------------------------------------------------

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

    // -- expressions ------------------------------------------------------

    /// The type context asked for, or the one the checker settled on where
    /// nothing did.
    fn settled_type(&mut self, wanted: Option<&Ty>, span: Span) -> Ty {
        match wanted {
            Some(wanted) => wanted.clone(),
            None => self.recorded(span),
        }
    }
}
