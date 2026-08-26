//! Types as written, resolved to types as held (LR54).
//!
//! Every annotation in a program passes through here exactly once: the ones
//! in a declaration when the table of declarations is built, and the ones
//! inside a body when that body is checked. Resolving one twice would report
//! a mistake in it twice.
//!
//! A path is resolved against what the module has in scope, so a type named
//! through an import reaches the module that declares it, and a name that is
//! not a type is reported here.

use std::collections::HashSet;

use luar_ast::TypeKind;
use luar_diagnostics::{Diagnostic, Span, codes};

use crate::aliases::Aliases;
use crate::modules::ModuleId;
use crate::names::{Names, Origin};
use crate::table::Kinds;
use crate::types::{Builtin, Primitive, Type};

/// Resolves the types written in one module.
pub struct Resolver<'a> {
    names: &'a Names,
    kinds: &'a Kinds,
    /// What every alias stands for (LR17.1). Empty while the table is being
    /// built, because building it is what works them out.
    aliases: &'a Aliases,
    module: ModuleId,
    /// The type parameters of the declarations being walked, innermost last
    /// (LR19).
    parameters: Vec<HashSet<String>>,
}

impl<'a> Resolver<'a> {
    #[must_use]
    pub fn new(names: &'a Names, kinds: &'a Kinds, aliases: &'a Aliases, module: ModuleId) -> Self {
        Self {
            names,
            kinds,
            aliases,
            module,
            parameters: Vec::new(),
        }
    }

    /// Brings the type parameters of a declaration into scope.
    pub fn enter(&mut self, parameters: &[String]) {
        self.parameters.push(parameters.iter().cloned().collect());
    }

    pub fn leave(&mut self) {
        self.parameters.pop();
    }

    /// Resolves one written type, reporting the paths in it that name no type.
    pub fn resolve(&mut self, ty: &luar_ast::Type, diagnostics: &mut Vec<Diagnostic>) -> Type {
        match &ty.kind {
            TypeKind::Path { segments, args } => {
                let args = args
                    .iter()
                    .map(|arg| self.resolve(arg, diagnostics))
                    .collect();
                self.path(segments, args, ty.span, diagnostics)
            }
            TypeKind::Optional(inner) => Type::Optional(Box::new(self.resolve(inner, diagnostics))),
            TypeKind::Union(members) => Type::Union(self.each(members, diagnostics)),
            TypeKind::Intersection(members) => Type::Intersection(self.each(members, diagnostics)),
            TypeKind::Tuple(members) => Type::Tuple(self.each(members, diagnostics)),
            TypeKind::Function {
                asynchronous,
                params,
                result,
            } => Type::Function {
                asynchronous: *asynchronous,
                params: self.each(params, diagnostics),
                result: Box::new(self.resolve(result, diagnostics)),
            },
            TypeKind::Array { element, .. } => {
                Type::Array(Box::new(self.resolve(element, diagnostics)))
            }
            TypeKind::Pointer { mutable, target } => Type::Pointer {
                mutable: *mutable,
                target: Box::new(self.resolve(target, diagnostics)),
            },
            TypeKind::Record(fields) => Type::Record(
                fields
                    .iter()
                    .map(|field| (field.name.clone(), self.resolve(&field.ty, diagnostics)))
                    .collect(),
            ),
            TypeKind::Error => Type::Unresolved,
        }
    }

    fn each(&mut self, types: &[luar_ast::Type], diagnostics: &mut Vec<Diagnostic>) -> Vec<Type> {
        types
            .iter()
            .map(|ty| self.resolve(ty, diagnostics))
            .collect()
    }

    /// What a path in a type names: a primitive, a builtin, a type parameter,
    /// a declaration of this module, or one of another module's (LR21.1).
    fn path(
        &mut self,
        segments: &[String],
        args: Vec<Type>,
        span: Span,
        diagnostics: &mut Vec<Diagnostic>,
    ) -> Type {
        let Some(first) = segments.first() else {
            return Type::Unresolved;
        };

        if segments.len() == 1 {
            if let Some(primitive) = Primitive::from_name(first) {
                return Type::Primitive(primitive);
            }
            if let Some(kind) = Builtin::from_name(first) {
                return Type::Builtin { kind, args };
            }
            if self.parameters.iter().any(|scope| scope.contains(first)) {
                return Type::Parameter(first.clone());
            }
        }

        match self.named(segments, args) {
            Some(ty) => ty,
            None => {
                diagnostics.push(Diagnostic::error(
                    codes::UNKNOWN_TYPE,
                    span,
                    format!("`{}` does not name a type", segments.join(".")),
                ));
                Type::Unresolved
            }
        }
    }

    /// The type a path names, if it names one. Reports nothing, so a caller
    /// reading a path where a type is not required can ask without turning
    /// the answer into a diagnostic.
    #[must_use]
    pub fn named(&self, segments: &[String], args: Vec<Type>) -> Option<Type> {
        let first = segments.first()?;

        // Where a name reaches another module, the type belongs to the module
        // that declares it, under the name it declares it as.
        let (module, name) = match self.names.scope(self.module).get(first).map(|b| &b.origin) {
            Some(Origin::Declared { .. }) if segments.len() == 1 => (self.module, first.clone()),
            Some(Origin::Imported { module, name }) if segments.len() == 1 => {
                (*module, name.clone())
            }
            Some(Origin::Namespace(module)) if segments.len() == 2 => {
                (*module, segments[1].clone())
            }
            _ => return None,
        };

        if !self.declares_type(module, &name) {
            return None;
        }

        // LR17.1: an alias stands for its target, so what a path naming one
        // resolves to is the target. Nothing past here sees the alias.
        Some(
            self.aliases
                .stands_for(module, &name, &args)
                .unwrap_or(Type::Named { module, name, args }),
        )
    }

    /// Whether `module` declares a type called `name` that this module may
    /// name. A function is a declaration too, and is not a type. Another
    /// module's declarations are the ones it exports (LR21, LR44).
    fn declares_type(&self, module: ModuleId, name: &str) -> bool {
        if !self.kinds.is_type(module, name) {
            return false;
        }

        module == self.module || self.names.scope(module).exports(name)
    }
}
