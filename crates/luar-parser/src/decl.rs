//! Declarations, and the module that holds them (LR9, LR21.3, LR44).

use luar_ast::{
    Block, Conditional, Constraint, Decorator, Enum, Extend, Field, Function, Import, ImportName,
    ImportNames, Interface, InterfaceMember, Item, Member, Module, Param, Property, Semantics,
    Setter, Struct, Type, TypeAlias, Variant, VariantPayload, Visibility,
};
use luar_diagnostics::{Span, codes};
use luar_lexer::{Keyword, TokenKind};

use crate::cursor::Cursor;
use crate::expr;
use crate::stmt;
use crate::ty;

/// A whole source file: declarations and module-level statements (LR21.3).
pub(crate) fn module(cursor: &mut Cursor) -> Module {
    let start = cursor.span();
    let mut items = Vec::new();

    while !cursor.at_end() {
        let before = cursor.mark();

        items.push(match item(cursor) {
            Some(item) => item,
            None => Item::Stmt(stmt::statement(cursor)),
        });

        while cursor.eat(TokenKind::Semicolon) {}

        // Nothing consumed means nothing can be read here.
        if cursor.stalled(before) {
            let here = cursor.span();
            if !cursor.reported_since(before) {
                cursor.error(
                    codes::EXPECTED_DECLARATION,
                    here,
                    "expected a declaration or a statement here",
                );
            }
            cursor.advance();
        }
    }

    Module {
        items,
        span: start.to(cursor.previous_span()),
    }
}

/// A declaration, if one starts here.
fn item(cursor: &mut Cursor) -> Option<Item> {
    let start = cursor.span();

    // LR48: conditional compilation selects declarations, so it is read where
    // one would be.
    if cursor.at_directive(Keyword::If) {
        return Some(Item::Conditional(conditional(cursor)));
    }

    // LR21.1: an import takes no decorators, so it is read before them.
    if cursor.kind() == TokenKind::Keyword(Keyword::Import) {
        return Some(Item::Import(import(cursor, start)));
    }

    let decorators = decorators(cursor);
    let mark = cursor.mark();
    let export_span = cursor.span();
    let exported = cursor.eat_keyword(Keyword::Export);

    // LR12.4, LR31: `const` and `ref` say how a struct is copied, and `const`
    // alone binds a value (LR5.2), so the `struct` decides.
    let semantics = if cursor.kind() == TokenKind::Keyword(Keyword::Const)
        && cursor.peek_kind(1) == TokenKind::Keyword(Keyword::Struct)
    {
        cursor.advance();
        Semantics::Const
    } else if cursor.eat_keyword(Keyword::Ref) {
        Semantics::Ref
    } else {
        Semantics::Value
    };

    if cursor.kind() == TokenKind::Keyword(Keyword::Struct) {
        return Some(Item::Struct(structure(
            cursor, start, decorators, exported, semantics,
        )));
    }

    if cursor.kind() == TokenKind::Keyword(Keyword::Enum) {
        return Some(Item::Enum(enumeration(cursor, start, decorators, exported)));
    }

    if cursor.kind() == TokenKind::Keyword(Keyword::Extend) {
        return Some(Item::Extend(extension(cursor, start, decorators, exported)));
    }

    if cursor.kind() == TokenKind::Keyword(Keyword::Type) {
        return Some(Item::TypeAlias(type_alias(
            cursor, start, decorators, exported,
        )));
    }

    let structural = cursor.eat_keyword(Keyword::Structural);
    if cursor.kind() == TokenKind::Keyword(Keyword::Interface) {
        return Some(Item::Interface(interface(
            cursor, start, decorators, exported, structural,
        )));
    }

    // LR52: `export` reaches a `const` value, and mutable module state stays
    // in the module that owns it.
    if exported
        && matches!(
            cursor.kind(),
            TokenKind::Keyword(Keyword::Const | Keyword::Local)
        )
    {
        return Some(Item::Stmt(exported_binding(cursor, export_span)));
    }

    cursor.rewind(mark);
    let decorated = decorators.first().map(|decorator| decorator.span);
    let function = declaration(cursor, decorators);

    // LR23: a decorator attaches to a declaration.
    if let (None, Some(span)) = (&function, decorated) {
        let here = cursor.span();
        cursor
            .error(
                codes::EXPECTED_DECLARATION,
                here,
                "a decorator attaches to a declaration, and this is not one",
            )
            .label(span, "this decorator has nothing to attach to");
    }

    function.map(Item::Function)
}

/// An `import` declaration (LR21.1).
fn import(cursor: &mut Cursor, start: Span) -> Import {
    cursor.advance();

    let names = if cursor.kind() == TokenKind::LeftBrace {
        let opened = cursor.span();
        cursor.advance();
        ImportNames::Named(import_names(cursor, opened))
    } else {
        ImportNames::Namespace(cursor.name().0)
    };

    if !cursor.eat_keyword(Keyword::From) {
        let here = cursor.span();
        cursor
            .error(
                codes::MALFORMED_IMPORT,
                here,
                "expected `from` and the module path",
            )
            .note("An import says where it comes from: `import { A } from \"./a\"` (LR21.1).");
    }

    let path_span = cursor.span();
    let path = if cursor.kind() == TokenKind::String {
        let text = cursor.text(path_span);
        cursor.advance();
        luar_lexer::value::string(text)
    } else {
        cursor.error(
            codes::MALFORMED_IMPORT,
            path_span,
            "expected the module path, written as a string",
        );
        None
    };

    Import {
        names,
        path,
        path_span,
        span: start.to(cursor.previous_span()),
    }
}

/// The names inside `import { ... }`, up to and including the closing brace.
fn import_names(cursor: &mut Cursor, opened: Span) -> Vec<ImportName> {
    let mut names = Vec::new();

    while !matches!(cursor.kind(), TokenKind::RightBrace | TokenKind::Eof) {
        let start = cursor.span();
        let name = cursor.name().0;
        let alias = cursor.eat_keyword(Keyword::As).then(|| cursor.name().0);
        names.push(ImportName {
            name,
            alias,
            span: start.to(cursor.previous_span()),
        });

        // Every turn of the loop consumes the comma or leaves, so a name that
        // could not be read ends the list rather than being read again.
        if !cursor.eat(TokenKind::Comma) {
            break;
        }
    }

    cursor.close(TokenKind::RightBrace, opened, "}");
    names
}

/// A module-level binding written after `export` (LR52).
fn exported_binding(cursor: &mut Cursor, export_span: Span) -> luar_ast::Stmt {
    if cursor.kind() == TokenKind::Keyword(Keyword::Local) {
        let here = cursor.span();
        cursor
            .error(
                codes::EXPORTED_MUTABLE_STATE,
                here,
                "mutable module state cannot be exported",
            )
            .label(export_span, "this is what exports it")
            .note(
                "A module exposes state it owns through functions, which gives it \
                 somewhere to put validation and synchronization (LR52).",
            );
    }

    let mut stmt = stmt::statement(cursor);
    if let luar_ast::StmtKind::Const { exported, .. } = &mut stmt.kind {
        *exported = true;
    }
    stmt
}

/// A function declaration, if one starts here.
fn declaration(cursor: &mut Cursor, decorators: Vec<Decorator>) -> Option<Function> {
    let start = cursor.span();
    let mark = cursor.mark();

    let exported = cursor.eat_keyword(Keyword::Export);
    let asynchronous = cursor.eat_keyword(Keyword::Async);
    let unsafe_ = cursor.eat_keyword(Keyword::Unsafe);
    let static_ = cursor.eat_keyword(Keyword::Static);

    if cursor.kind() != TokenKind::Keyword(Keyword::Function) {
        // Only `unsafe` can begin something else, and `export` can only begin
        // a declaration, so anything else here is not one.
        if exported || asynchronous || static_ {
            let here = cursor.span();
            cursor
                .error(
                    codes::EXPECTED_DECLARATION,
                    here,
                    "expected `function` after this modifier",
                )
                .label(start, "these modifiers describe a declaration");
            return None;
        }
        cursor.rewind(mark);
        return None;
    }

    cursor.advance();

    // LR46, LR89.1: a foreign declaration is its own form.
    let foreign = decorators
        .iter()
        .find(|decorator| decorator.name == "extern");

    if let Some(foreign) = foreign {
        if !unsafe_ {
            let span = foreign.span;
            cursor
                .error(
                    codes::EXTERN_WITHOUT_UNSAFE,
                    span,
                    "a foreign declaration must be `unsafe`",
                )
                .note(
                    "The compiler can verify nothing about the callee, so the declaration says \n                     so: `@extern(\"c\") unsafe function` (LR46).",
                );
        }
        if foreign.args.is_empty() {
            let span = foreign.span;
            cursor.error(
                codes::EXTERN_WITHOUT_UNSAFE,
                span,
                "a foreign declaration states which ABI it uses",
            );
        }
    }

    // LR60: an intrinsic states a signature and no more.
    let bodied = foreign.is_none()
        && !decorators
            .iter()
            .any(|decorator| decorator.name == "intrinsic");

    Some(function(
        cursor,
        start,
        Modifiers {
            decorators,
            exported,
            asynchronous,
            unsafe_,
            static_,
        },
        bodied,
    ))
}

struct Modifiers {
    decorators: Vec<Decorator>,
    exported: bool,
    asynchronous: bool,
    unsafe_: bool,
    static_: bool,
}

/// A function declaration. `body` is read unless the caller says the
/// declaration states a signature and no more (LR18, LR46).
fn function(cursor: &mut Cursor, start: Span, modifiers: Modifiers, bodied: bool) -> Function {
    // A qualified name declares a member of the type it names (LR20, LR42).
    let mut name = vec![cursor.name().0];
    while cursor.eat(TokenKind::Dot) {
        name.push(cursor.name().0);
    }

    let type_params = type_parameters(cursor);
    let params = parameters(cursor);
    let result = cursor.eat(TokenKind::Colon).then(|| ty::ty(cursor));
    let constraints = where_clause(cursor);

    let body = bodied.then(|| {
        let body = stmt::block(cursor);
        close(cursor, start, "function");
        body
    });

    Function {
        decorators: modifiers.decorators,
        exported: modifiers.exported,
        asynchronous: modifiers.asynchronous,
        unsafe_: modifiers.unsafe_,
        static_: modifiers.static_,
        name,
        type_params,
        constraints,
        params,
        result,
        body,
        span: start.to(cursor.previous_span()),
    }
}

/// `where T: Comparable, U: Hashable & Display` (LR19).
fn where_clause(cursor: &mut Cursor) -> Vec<Constraint> {
    if !cursor.eat_keyword(Keyword::Where) {
        return Vec::new();
    }

    let mut constraints = Vec::new();
    loop {
        let start = cursor.span();
        let parameter = cursor.name().0;

        if !cursor.eat(TokenKind::Colon) {
            let here = cursor.span();
            cursor
                .error(codes::EXPECTED_TYPE, here, "expected `:` and a bound")
                .note("A bound is written `T: Interface` (LR19).");
        }

        let bound = ty::ty(cursor);
        constraints.push(Constraint {
            parameter,
            bound,
            span: start.to(cursor.previous_span()),
        });

        if !cursor.eat(TokenKind::Comma) {
            break;
        }
    }

    constraints
}

/// `(a: int, b: int = 0, ...rest: string)` (LR9.4, LR9.6).
pub(crate) fn parameters(cursor: &mut Cursor) -> Vec<Param> {
    let opened = cursor.span();

    if !cursor.eat(TokenKind::LeftParen) {
        let here = cursor.span();
        cursor.error(codes::EXPECTED_DECLARATION, here, "expected `(`");
        return Vec::new();
    }

    let mut params = Vec::new();
    while !matches!(cursor.kind(), TokenKind::RightParen | TokenKind::Eof) {
        let start = cursor.span();
        let variadic = cursor.eat(TokenKind::DotDotDot);
        let binding = stmt::binding(cursor);
        let ty = cursor.eat(TokenKind::Colon).then(|| ty::ty(cursor));
        // LR9.4: a default is evaluated at the call site when omitted.
        let default = cursor
            .eat(TokenKind::Equals)
            .then(|| expr::expression(cursor));

        params.push(Param {
            binding,
            ty,
            default,
            variadic,
            span: start.to(cursor.previous_span()),
        });

        if !cursor.eat(TokenKind::Comma) {
            break;
        }
    }

    cursor.close(TokenKind::RightParen, opened, ")");
    params
}

/// `struct`, `const struct`, and `ref struct` (LR12.2, LR12.4, LR31).
fn structure(
    cursor: &mut Cursor,
    start: Span,
    decorators: Vec<Decorator>,
    exported: bool,
    semantics: Semantics,
) -> Struct {
    cursor.advance();

    let name = cursor.name().0;
    let type_params = type_parameters(cursor);

    // LR18: what the struct claims to implement, checked when types are.
    let mut implements = Vec::new();
    if cursor.eat_keyword(Keyword::Implements) {
        implements.push(ty::ty(cursor));
        while cursor.eat(TokenKind::Comma) {
            implements.push(ty::ty(cursor));
        }
    }

    let mut members = Vec::new();
    while !matches!(
        cursor.kind(),
        TokenKind::Keyword(Keyword::End) | TokenKind::Eof
    ) {
        let before = cursor.mark();
        members.push(member(cursor));

        if cursor.stalled(before) {
            cursor.advance();
        }
    }

    if !cursor.eat_keyword(Keyword::End) {
        let here = cursor.span();
        cursor
            .error(codes::UNCLOSED_DELIMITER, start, "expected `end`")
            .label(here, "expected `end` before here");
    }

    Struct {
        decorators,
        exported,
        semantics,
        name,
        type_params,
        implements,
        members,
        span: start.to(cursor.previous_span()),
    }
}

/// A field, a method, or a property (LR12.2, LR42, LR43).
fn member(cursor: &mut Cursor) -> Member {
    let start = cursor.span();
    let decorators = decorators(cursor);

    // LR44: a member is public by default, and may say otherwise.
    let visibility = match cursor.kind() {
        TokenKind::Keyword(Keyword::Private) => Some(Visibility::Private),
        TokenKind::Keyword(Keyword::Internal) => Some(Visibility::Internal),
        TokenKind::Keyword(Keyword::Public) => Some(Visibility::Public),
        _ => None,
    };
    if visibility.is_some() {
        cursor.advance();
    }

    if cursor.kind() == TokenKind::Keyword(Keyword::Property) {
        reject_finalizer_target(cursor, &decorators);
        return Member::Property(property(cursor, start, visibility));
    }

    // A method is an ordinary function declaration, modifiers and all (LR42).
    if let Some(function) = declaration(cursor, decorators.clone()) {
        return Member::Function {
            visibility,
            function,
        };
    }

    reject_finalizer_target(cursor, &decorators);
    Member::Field(field(cursor, start, visibility))
}

fn reject_finalizer_target(cursor: &mut Cursor, decorators: &[Decorator]) {
    for decorator in decorators
        .iter()
        .filter(|decorator| decorator.name == "finalizer")
    {
        cursor
            .error(
                codes::FINALIZER_TARGET,
                decorator.span,
                "a field or property cannot be a finalizer",
            )
            .note("`@finalizer` applies to an instance function in a `ref struct` (LR51).");
    }
}

/// `name: T`, with a default where it has one (LR12.2).
fn field(cursor: &mut Cursor, start: Span, visibility: Option<Visibility>) -> Field {
    let name = cursor.name().0;

    // Without the `:` there is no type to read, and reading one anyway would
    // report the same mistake twice.
    if !cursor.eat(TokenKind::Colon) {
        let here = cursor.span();
        cursor
            .error(codes::EXPECTED_TYPE, here, "expected `:` and a field type")
            .note("A field is written `name: T`; `:` introduces a type (LR89.1).");

        return Field {
            visibility,
            name,
            ty: Type::new(luar_ast::TypeKind::Error, here),
            default: None,
            span: start.to(cursor.previous_span()),
        };
    }

    let ty = ty::ty(cursor);
    let default = cursor
        .eat(TokenKind::Equals)
        .then(|| expr::expression(cursor));

    Field {
        visibility,
        name,
        ty,
        default,
        span: start.to(cursor.previous_span()),
    }
}

/// `property name: T get ... end [set (v) ... end] end` (LR43).
fn property(cursor: &mut Cursor, start: Span, visibility: Option<Visibility>) -> Property {
    cursor.advance();

    let name = cursor.name().0;
    if !cursor.eat(TokenKind::Colon) {
        let here = cursor.span();
        cursor.error(codes::EXPECTED_TYPE, here, "expected `:` and a type");
    }
    let ty = ty::ty(cursor);

    let get = if cursor.eat_contextual("get") {
        let body = stmt::block(cursor);
        close(cursor, start, "get");
        body
    } else {
        let here = cursor.span();
        cursor
            .error(codes::EXPECTED_ACCESSOR, here, "a property needs a `get`")
            .label(start, "this property has none")
            .note("A property is read like a field, so it must say what reading it does (LR43).");
        Block {
            stmts: Vec::new(),
            span: cursor.span(),
        }
    };

    let set = cursor.eat_contextual("set").then(|| setter(cursor));

    close(cursor, start, "property");

    Property {
        visibility,
        name,
        ty,
        get,
        set,
        span: start.to(cursor.previous_span()),
    }
}

/// `set (newValue) ... end` (LR43). The setter is explicit, and names the
/// value being assigned.
fn setter(cursor: &mut Cursor) -> Setter {
    let start = cursor.previous_span();
    let opened = cursor.span();

    let param = if cursor.eat(TokenKind::LeftParen) {
        let param = cursor.name().0;
        cursor.close(TokenKind::RightParen, opened, ")");
        param
    } else {
        let here = cursor.span();
        cursor
            .error(
                codes::EXPECTED_ACCESSOR,
                here,
                "a setter names the value being assigned",
            )
            .note("Write `set (newValue)` (LR43).");
        String::new()
    };

    let body = stmt::block(cursor);
    close(cursor, start, "set");

    Setter {
        param,
        body,
        span: start.to(cursor.previous_span()),
    }
}

/// `<T, U>` (LR19). Constraints are `where` clauses, which arrive with the
/// checking that uses them.
fn type_parameters(cursor: &mut Cursor) -> Vec<String> {
    if !cursor.eat(TokenKind::Lt) {
        return Vec::new();
    }

    let opened = cursor.previous_span();
    let mut params = Vec::new();
    while !cursor.at_type_args_close() && !cursor.at_end() {
        params.push(cursor.name().0);
        if !cursor.eat(TokenKind::Comma) {
            break;
        }
    }

    if !cursor.eat_type_args_close() {
        let here = cursor.span();
        cursor
            .error(codes::UNCLOSED_DELIMITER, opened, "expected `>`")
            .label(here, "expected `>` before here");
    }

    params
}

/// Consumes the `end` closing `opened`, or says what is unclosed.
fn close(cursor: &mut Cursor, opened: Span, construct: &str) {
    if cursor.eat_keyword(Keyword::End) {
        return;
    }

    let here = cursor.span();
    cursor
        .error(codes::UNCLOSED_DELIMITER, opened, "expected `end`")
        .label(
            here,
            format!("expected `end` for this `{construct}` before here"),
        );
}

/// `enum Name ... end`, whose variants may carry data (LR15).
fn enumeration(
    cursor: &mut Cursor,
    start: Span,
    decorators: Vec<Decorator>,
    exported: bool,
) -> Enum {
    cursor.advance();

    let name = cursor.name().0;
    let type_params = type_parameters(cursor);

    let mut variants = Vec::new();
    while !matches!(
        cursor.kind(),
        TokenKind::Keyword(Keyword::End) | TokenKind::Eof
    ) {
        let before = cursor.mark();
        variants.push(variant(cursor));

        if cursor.stalled(before) {
            cursor.advance();
        }
    }

    close(cursor, start, "enum");

    Enum {
        decorators,
        exported,
        name,
        type_params,
        variants,
        span: start.to(cursor.previous_span()),
    }
}

/// `Quit`, `Write(string)`, or `Move { x: int, y: int }` (LR15.1, LR15.2).
fn variant(cursor: &mut Cursor) -> Variant {
    let start = cursor.span();
    let name = cursor.name().0;

    let payload = match cursor.kind() {
        TokenKind::LeftParen => Some(VariantPayload::Tuple(variant_types(cursor))),
        TokenKind::LeftBrace => Some(VariantPayload::Record(ty::record_fields(cursor))),
        _ => None,
    };

    Variant {
        name,
        payload,
        span: start.to(cursor.previous_span()),
    }
}

/// `(A, B)`, the types a variant carries by position.
fn variant_types(cursor: &mut Cursor) -> Vec<Type> {
    let opened = cursor.span();
    cursor.advance();

    let mut types = Vec::new();
    while !matches!(cursor.kind(), TokenKind::RightParen | TokenKind::Eof) {
        types.push(ty::ty(cursor));
        if !cursor.eat(TokenKind::Comma) {
            break;
        }
    }

    cursor.close(TokenKind::RightParen, opened, ")");
    types
}

/// `interface Name ... end`, and `structural interface` (LR18).
fn interface(
    cursor: &mut Cursor,
    start: Span,
    decorators: Vec<Decorator>,
    exported: bool,
    structural: bool,
) -> Interface {
    cursor.advance();

    let name = cursor.name().0;
    let type_params = type_parameters(cursor);

    let mut members = Vec::new();
    while !matches!(
        cursor.kind(),
        TokenKind::Keyword(Keyword::End) | TokenKind::Eof
    ) {
        let before = cursor.mark();
        members.push(interface_member(cursor));

        if cursor.stalled(before) {
            cursor.advance();
        }
    }

    close(cursor, start, "interface");

    Interface {
        decorators,
        exported,
        structural,
        name,
        type_params,
        members,
        span: start.to(cursor.previous_span()),
    }
}

/// A required method, which has no body, or a required property (LR18).
fn interface_member(cursor: &mut Cursor) -> InterfaceMember {
    let start = cursor.span();
    let decorators = decorators(cursor);
    let asynchronous = cursor.eat_keyword(Keyword::Async);

    if cursor.eat_keyword(Keyword::Function) {
        return InterfaceMember::Function(function(
            cursor,
            start,
            Modifiers {
                decorators,
                exported: false,
                asynchronous,
                unsafe_: false,
                static_: false,
            },
            false,
        ));
    }

    let name = cursor.name().0;
    if !cursor.eat(TokenKind::Colon) {
        let here = cursor.span();
        cursor
            .error(codes::EXPECTED_TYPE, here, "expected `:` and a type")
            .note("An interface member is a function signature or a property `name: T` (LR18).");
    }

    let ty = ty::ty(cursor);
    InterfaceMember::Property {
        name,
        ty,
        span: start.to(cursor.previous_span()),
    }
}

/// `extend Name<T> for Type ... end` (LR20).
fn extension(
    cursor: &mut Cursor,
    start: Span,
    decorators: Vec<Decorator>,
    exported: bool,
) -> Extend {
    cursor.advance();

    let name = cursor.name().0;
    let type_params = type_parameters(cursor);

    if !cursor.eat_keyword(Keyword::For) {
        let here = cursor.span();
        cursor
            .error(
                codes::EXPECTED_DECLARATION,
                here,
                "expected `for` and a type",
            )
            .note(
                "An extension block names itself and what it extends: `extend Name for T` (LR20).",
            );
    }

    let target = ty::ty(cursor);

    let mut functions = Vec::new();
    while !matches!(
        cursor.kind(),
        TokenKind::Keyword(Keyword::End) | TokenKind::Eof
    ) {
        let before = cursor.mark();

        let member_decorators = self::decorators(cursor);
        match declaration(cursor, member_decorators) {
            Some(function) => functions.push(function),
            None => {
                let here = cursor.span();
                if !cursor.reported_since(before) {
                    cursor
                        .error(
                            codes::EXPECTED_DECLARATION,
                            here,
                            "an extension block holds functions",
                        )
                        .note("Extension methods add no stored fields (LR20).");
                }
            }
        }

        if cursor.stalled(before) {
            cursor.advance();
        }
    }

    close(cursor, start, "extend");

    Extend {
        decorators,
        exported,
        name,
        type_params,
        target,
        functions,
        span: start.to(cursor.previous_span()),
    }
}

/// `type Name = T` (LR17.1).
fn type_alias(
    cursor: &mut Cursor,
    start: Span,
    decorators: Vec<Decorator>,
    exported: bool,
) -> TypeAlias {
    cursor.advance();

    let name = cursor.name().0;
    let type_params = type_parameters(cursor);

    if !cursor.eat(TokenKind::Equals) {
        let here = cursor.span();
        cursor.error(codes::EXPECTED_TYPE, here, "expected `=` and a type");
    }

    let target = ty::ty(cursor);

    TypeAlias {
        decorators,
        exported,
        name,
        type_params,
        target,
        span: start.to(cursor.previous_span()),
    }
}

/// The decorators written before a declaration (LR23).
fn decorators(cursor: &mut Cursor) -> Vec<Decorator> {
    let mut decorators = Vec::new();

    while cursor.kind() == TokenKind::At {
        let start = cursor.span();
        cursor.advance();

        let name = cursor.name().0;
        let args = if cursor.kind() == TokenKind::LeftParen {
            expr::arguments(cursor)
        } else {
            Vec::new()
        };

        decorators.push(Decorator {
            name,
            args,
            span: start.to(cursor.previous_span()),
        });
    }

    decorators
}

/// `#if ... #elseif ... #else ... #end`, around declarations (LR48).
fn conditional(cursor: &mut Cursor) -> Conditional {
    let start = cursor.span();
    cursor.advance();
    cursor.advance();

    let mut branches = vec![(expr::expression(cursor), items_until_directive(cursor))];
    let mut otherwise = None;

    loop {
        if cursor.eat_directive(Keyword::Elseif) {
            let condition = expr::expression(cursor);
            branches.push((condition, items_until_directive(cursor)));
            continue;
        }
        if cursor.eat_directive(Keyword::Else) {
            otherwise = Some(items_until_directive(cursor));
        }
        break;
    }

    if !cursor.eat_directive(Keyword::End) {
        let here = cursor.span();
        cursor
            .error(codes::UNCLOSED_DELIMITER, start, "expected `#end`")
            .label(here, "expected `#end` before here");
    }

    Conditional {
        branches,
        otherwise,
        span: start.to(cursor.previous_span()),
    }
}

/// Declarations up to the next `#` directive, which the caller consumes.
fn items_until_directive(cursor: &mut Cursor) -> Vec<Item> {
    let mut items = Vec::new();

    while !matches!(cursor.kind(), TokenKind::Hash | TokenKind::Eof) {
        let before = cursor.mark();

        items.push(match item(cursor) {
            Some(item) => item,
            None => Item::Stmt(stmt::statement(cursor)),
        });

        while cursor.eat(TokenKind::Semicolon) {}

        if cursor.stalled(before) {
            cursor.advance();
        }
    }

    items
}
