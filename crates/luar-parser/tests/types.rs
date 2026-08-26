//! Checks the type grammar of LR89 and the readings LR89.1 settles.

use luar_diagnostics::FileId;

const FILE: FileId = FileId(0);

/// Types are written in annotations, so they are read through a cast, which
/// is the one expression that takes one today.
fn shape(source: &str) -> String {
    let parsed = luar_parser::expression(&format!("x as {source}"), FILE);
    assert_eq!(
        parsed
            .diagnostics
            .iter()
            .map(|d| d.code.to_string())
            .collect::<Vec<_>>(),
        Vec::<String>::new(),
        "`{source}` did not parse as a type"
    );

    match parsed.tree.kind {
        luar_ast::ExprKind::Cast { ty, .. } => render(&ty),
        other => panic!("expected a cast, got {other:?}"),
    }
}

fn codes(source: &str) -> Vec<String> {
    luar_parser::expression(&format!("x as {source}"), FILE)
        .diagnostics
        .iter()
        .map(|d| d.code.to_string())
        .collect()
}

fn render(ty: &luar_ast::Type) -> String {
    use luar_ast::TypeKind;

    match &ty.kind {
        TypeKind::Path { segments, args } => {
            let name = segments.join(".");
            if args.is_empty() {
                name
            } else {
                format!("{name}<{}>", rendered(args))
            }
        }
        TypeKind::Optional(inner) => format!("{}?", render(inner)),
        TypeKind::Union(members) => format!("({})", joined(members, " | ")),
        TypeKind::Intersection(members) => format!("({})", joined(members, " & ")),
        TypeKind::Tuple(members) => format!("({})", rendered(members)),
        TypeKind::Function {
            asynchronous,
            params,
            result,
        } => format!(
            "{}({}) -> {}",
            if *asynchronous { "async " } else { "" },
            rendered(params),
            render(result)
        ),
        TypeKind::Array { element, length } => {
            format!("[{}; {:?}]", render(element), length.kind)
        }
        TypeKind::Pointer { mutable, target } => format!(
            "*{} {}",
            if *mutable { "mut" } else { "const" },
            render(target)
        ),
        TypeKind::Record(fields) => {
            let fields: Vec<String> = fields
                .iter()
                .map(|field| format!("{}: {}", field.name, render(&field.ty)))
                .collect();
            format!("{{{}}}", fields.join(", "))
        }
        TypeKind::Error => "(error)".to_owned(),
    }
}

fn rendered(types: &[luar_ast::Type]) -> String {
    joined(types, ", ")
}

fn joined(types: &[luar_ast::Type], separator: &str) -> String {
    types.iter().map(render).collect::<Vec<_>>().join(separator)
}

/// LR17.2, LR17.3, LR8: unions of intersections of optionals, loosest first.
#[test]
fn unions_are_looser_than_intersections_and_optionals() {
    assert_eq!(shape("string | u64"), "(string | u64)");
    assert_eq!(shape("Named & Identified"), "(Named & Identified)");
    assert_eq!(shape("A | B & C"), "(A | (B & C))");
    assert_eq!(shape("A & B?"), "(A & B?)");
    assert_eq!(shape("string?"), "string?");
}

/// LR19, LR21.1: type arguments, and names qualified by module.
#[test]
fn paths_carry_type_arguments() {
    assert_eq!(shape("Map<string, int>"), "Map<string, int>");
    assert_eq!(shape("json.Value"), "json.Value");
    assert_eq!(shape("Result<User, Error>?"), "Result<User, Error>?");
}

/// `Map<string, List<int>>` ends in one `>>` token, which the parser splits
/// because it knows it is closing a type-argument list.
#[test]
fn nested_type_arguments_close_on_a_shift_token() {
    assert_eq!(shape("Map<string, List<int>>"), "Map<string, List<int>>");
    assert_eq!(shape("List<List<List<int>>>"), "List<List<List<int>>>");
}

/// LR14, LR89.1: a parenthesized type list is a tuple unless `->` follows.
#[test]
fn a_parenthesized_list_is_a_tuple_unless_an_arrow_follows() {
    assert_eq!(shape("(int, string)"), "(int, string)");
    assert_eq!(shape("()"), "()");
    assert_eq!(shape("(Request) -> Response"), "(Request) -> Response");
    assert_eq!(
        shape("async (Request) -> Response"),
        "async (Request) -> Response"
    );
    // One type in parentheses is that type, not a one-element tuple.
    assert_eq!(shape("(int)"), "int");
}

/// LR71, LR72, LR12.1: arrays, pointers, and structural records.
#[test]
fn arrays_pointers_and_records() {
    assert_eq!(shape("[u8; 4]"), "[u8; Integer(4)]");
    assert_eq!(shape("*const u8"), "*const u8");
    assert_eq!(shape("*mut CTime"), "*mut CTime");
    assert_eq!(
        shape("{ id: u64, email: string? }"),
        "{id: u64, email: string?}"
    );
}

/// The first error is the real one. A parse that has already gone wrong may
/// report more after it, and the code that matters is the one for the rule
/// that was broken.
#[test]
fn what_is_not_a_type_is_reported() {
    assert_eq!(codes("1").first().map(String::as_str), Some("LR0126"));
    assert_eq!(codes("*u8").first().map(String::as_str), Some("LR0126"));
    assert_eq!(codes("[u8]").first().map(String::as_str), Some("LR0126"));
    assert_eq!(
        codes("Map<string").first().map(String::as_str),
        Some("LR0124")
    );
}
