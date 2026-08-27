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
    BinaryOp as AstBinary, Binding, Block, Expr, ExprKind, Stmt, StmtKind, UnaryOp as AstUnary,
};
use luar_diagnostics::Span;
use luar_sema::facts::Facts;

use luar_sema::types::Type;

use crate::inst::{BinaryOp, Const, Inst, InstKind, Terminator, Trap, UnaryOp, Value};
use crate::lower::Gap;
use crate::lower::types::{self, Ids};
use crate::program::{BlockId, Function};
use crate::ty::Ty;

/// A binding, told apart from every other one with its name (LR53).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct Var(u32);

/// What lowering a body needs from the rest of the program.
pub(super) struct Context<'a> {
    pub facts: &'a Facts,
    pub ids: &'a Ids,
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
    /// The value each binding currently holds.
    defs: HashMap<Var, Value>,
    next_var: u32,
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
            defs: HashMap::new(),
            next_var: 0,
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

    fn missing_type(&mut self, span: Span, what: impl Into<String>) -> Ty {
        self.gap(span, what);
        Ty::Never
    }

    /// The type both operands of `op` are read at.
    ///
    /// A literal takes its type from the other operand where the other one
    /// has one, which is the same rule the checker applied (LR39).
    fn operand_type(&mut self, left: &Expr, right: &Expr) -> Ty {
        let held = |facts: &Facts, expr: &Expr| facts.type_of(expr.span).cloned();
        let literal = |ty: &Option<Type>| {
            matches!(
                ty,
                Some(Type::IntegerLiteral(_) | Type::FloatLiteral | Type::SequenceLiteral(_))
                    | None
            )
        };

        let held_left = held(self.context.facts, left);
        let held_right = held(self.context.facts, right);
        let span = if literal(&held_left) && !literal(&held_right) {
            right.span
        } else {
            left.span
        };
        self.recorded(span)
    }

    // -- statements -------------------------------------------------------

    fn block(&mut self, block: &Block) {
        self.scopes.push(Vec::new());
        for stmt in &block.stmts {
            if self.left {
                // LR50: nothing after a block was left runs, so nothing after
                // it is lowered.
                break;
            }
            self.stmt(stmt);
        }
        self.scopes.pop();
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
            StmtKind::Expr(expr) => {
                self.expr(expr, None);
            }
            StmtKind::Error => {}
            _ => self.gap(stmt.span, "a statement"),
        }
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
        match op {
            AstBinary::And | AstBinary::Or | AstBinary::Coalesce => {
                self.missing(span, "a short-circuiting operator")
            }
            _ => {
                let Some(lowered) = binary_op(op) else {
                    return self.missing(span, "a binary operator");
                };
                let ty = self.recorded(span);
                let operand = self.operand_type(left, right);
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
            _ => value,
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
