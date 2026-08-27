//! The diagnostic code registry.

use crate::code::Code;

/// One row of the registry.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Entry {
    pub code: Code,
    /// The constant this code is spelled as in compiler source.
    pub name: &'static str,
    /// The spec section stating the rule, such as `"LR11.1"`. Empty if retired.
    pub spec: &'static str,
    /// One line saying what the rule is.
    pub summary: &'static str,
    pub retired: bool,
}

impl Entry {
    #[must_use]
    pub const fn is_active(&self) -> bool {
        !self.retired
    }
}

/// Declares a registry: the code constants, the table describing them, and the
/// lookups over it.
macro_rules! registry {
    ($(
        $status:ident $number:literal => $name:ident, $spec:literal, $summary:literal;
    )*) => {
        $(declare_code!($status $name = $number);)*

        /// Every code ever assigned, active or retired, ascending by number.
        pub static TABLE: &[Entry] = &[$(Entry {
            code: Code::new($number),
            name: stringify!($name),
            spec: $spec,
            summary: $summary,
            retired: is_retired!($status),
        }),*];

        const _: () = {
            let mut i = 1;
            while i < TABLE.len() {
                assert!(
                    TABLE[i - 1].code.number() < TABLE[i].code.number(),
                    "diagnostic codes must be listed in ascending order, and a \
                     number is never reused once assigned"
                );
                i += 1;
            }
        };

        /// The entry for `number`, whether it is active or retired.
        #[must_use]
        pub fn lookup(number: u16) -> Option<&'static Entry> {
            TABLE
                .binary_search_by_key(&number, |entry| entry.code.number())
                .ok()
                .map(|i| &TABLE[i])
        }

        /// The rules the compiler currently enforces.
        pub fn active() -> impl Iterator<Item = &'static Entry> {
            TABLE.iter().filter(|entry| entry.is_active())
        }
    };
}

macro_rules! declare_code {
    (active $name:ident = $number:literal) => {
        pub const $name: Code = Code::new($number);
    };
    (retired $name:ident = $number:literal) => {};
}

macro_rules! is_retired {
    (active) => {
        false
    };
    (retired) => {
        true
    };
}

registry! {
    active 114 => FLOAT_DIVISION_ON_INTEGERS, "LR11.1",
        "`/` is not defined for two integers; `//` is integer division.";
    active 115 => RESERVED_WORD, "LR81",
        "A word reserved without a meaning cannot be used as an identifier.";
    active 116 => MALFORMED_NUMBER, "LR4.3",
        "A numeric literal must be written in one of the forms the spec states.";
    active 117 => INTEGER_LITERAL_TOO_LARGE, "LR4.3",
        "An integer literal must fit in the widest integer type, which is 64 bits.";
    active 118 => UNTERMINATED_LITERAL, "LR4.5",
        "A string, byte string, or character literal must be closed.";
    active 119 => INVALID_ESCAPE, "LR4.5",
        "An escape sequence must be one the spec defines, and well formed.";
    active 120 => STRING_NOT_UTF8, "LR4.5",
        "A string holds valid UTF-8, so a byte escape past 0x7F needs a byte string.";
    active 121 => MALFORMED_CHAR, "LR6.1",
        "A character literal holds exactly one Unicode scalar value.";
    active 122 => UNTERMINATED_COMMENT, "LR3.3",
        "A block comment must be closed, at the level it was opened.";
    active 123 => EXPECTED_EXPRESSION, "LR89.2",
        "A value is required here, and what is written is not one.";
    active 124 => UNCLOSED_DELIMITER, "LR89.2",
        "An opening delimiter or block must be closed by its matching terminator.";
    active 125 => CHAINED_OPERATOR, "LR11.7",
        "Comparison and range operators do not chain.";
    active 126 => EXPECTED_TYPE, "LR89.2",
        "A type is required here, and what is written is not one.";
    active 127 => INVALID_ASSIGNMENT_TARGET, "LR89.2",
        "Assignment writes to a name, a field, or an element, and nothing else.";
    active 128 => STATEMENT_WITHOUT_EFFECT, "LR89.1",
        "An expression used as a statement must be a call, so that it does something.";
    active 129 => EXPECTED_PATTERN, "LR16.2",
        "A pattern is required here, and what is written is not one.";
    active 130 => MIXED_MATCH_ARMS, "LR16.1",
        "One `match` uses block cases or `=>` cases, never both.";
    active 131 => REPEATED_REST_PATTERN, "LR16.2",
        "A sequence pattern has at most one rest pattern.";
    active 132 => EXPECTED_DECLARATION, "LR89.2",
        "A module holds declarations and statements, and this is neither.";
    active 133 => EXPECTED_ACCESSOR, "LR43",
        "A property says what reading it does, and a setter names what is assigned.";
    active 134 => EXTERN_WITHOUT_UNSAFE, "LR46",
        "A foreign declaration states an ABI and is `unsafe`, since neither is verifiable.";
    active 135 => MALFORMED_IMPORT, "LR21.1",
        "An import names what it binds, then `from`, then the module path as a string.";
    active 136 => UNRESOLVED_IMPORT, "LR21.1",
        "An import path must name a module the compiler can read.";
    active 137 => NAME_NOT_EXPORTED, "LR21.1",
        "A named import must name a declaration the module exports.";
    active 138 => NAME_NOT_IN_SCOPE, "LR54",
        "A name in value position must be declared, imported, or predeclared.";
    active 139 => IMPLICIT_GLOBAL, "LR52",
        "Assignment declares nothing; the name must already be in scope.";
    active 140 => PARAMETER_REDECLARED, "LR53",
        "A parameter list names each parameter once.";
    active 141 => EXPORTED_MUTABLE_STATE, "LR52",
        "`export` reaches declarations and `const` values, and not mutable state.";
    active 142 => UNSAFE_IMPORT_CYCLE, "LR21.2",
        "Modules in a cycle must have an initialization order, and this pair has none.";
    active 143 => UNKNOWN_TYPE, "LR54",
        "A name in a type must be a primitive, a declaration, an import, or predeclared.";
    active 144 => CONDITION_NOT_BOOL, "LR4.2",
        "A condition and the operands of `and`, `or`, and `not` have type `bool`.";
    active 145 => TYPE_MISMATCH, "LR5.1",
        "A binding declared with a type takes values of that type.";
    active 146 => NO_SUCH_MEMBER, "LR12.2",
        "A field read from a value must be one the type declares.";
    active 147 => ARGUMENT_COUNT, "LR9.1",
        "A call passes an argument for every parameter without a default.";
    active 148 => ARGUMENT_TYPE, "LR9.1",
        "An argument has the type its parameter declares.";
    active 149 => PRIVATE_MEMBER, "LR44",
        "A `private` member is reachable only inside the module that declares it.";
    active 150 => AMBIGUOUS_EXTENSION, "LR20",
        "Two extension blocks in scope offering one method for one type is decided by naming one.";
    active 151 => EXTENSION_OVERRIDES_MEMBER, "LR20",
        "An extension adds members to a type and never replaces one it already has.";
    active 152 => METHOD_OUTSIDE_ITS_MODULE, "LR20",
        "A method is attached to a type in the module declaring it; elsewhere an extension block adds one.";
    active 153 => MISSING_FIELD, "LR12.2",
        "A struct literal gives a value for every field without a default.";
    active 154 => UNKNOWN_FIELD, "LR12.2",
        "A struct literal names only fields the struct declares.";
    active 155 => DUPLICATE_MEMBER, "LR12.2",
        "A type declares each member once, whether written in its body or attached outside it.";
    active 156 => NO_SUCH_METHOD, "LR76",
        "A method called on a value is one the type declares or an extension block in scope adds.";
    active 157 => INDISTINGUISHABLE_OVERLOADS, "LR40",
        "Overloads of one name differ in their parameters; a result does not tell two apart.";
    active 158 => NO_MATCHING_OVERLOAD, "LR40",
        "A call matches one of the overloads its name has.";
    active 159 => AMBIGUOUS_OVERLOAD, "LR40",
        "A call matching more than one overload has no one meaning.";
    active 160 => MEMBER_THROUGH_OPTIONAL, "LR8",
        "An optional is narrowed, or reached through `?.`, before a member of it is read.";
    active 161 => MEMBER_THROUGH_UNION, "LR17.2",
        "A union is narrowed to one member type before anything only that type has is used.";
    active 162 => INTERFACE_NOT_SATISFIED, "LR18",
        "A type saying it implements an interface has every member that interface requires.";
    active 163 => STRUCTURAL_PROPERTY, "LR18",
        "A structural interface states behavior, and claims nothing about stored layout.";
    active 164 => MATCH_NOT_EXHAUSTIVE, "LR16.4",
        "A match covers every value its scrutinee can hold.";
    active 165 => UNREACHABLE_CASE, "LR16.4",
        "A case an earlier one already covers never runs.";
    active 166 => CIRCULAR_ALIAS, "LR17.1",
        "An alias names what another type is, and cannot name itself.";
    active 167 => INTEGER_DIVISION_OPERANDS, "LR11.1",
        "`//` is integer division, and is defined on integers alone.";
    active 168 => FALLIBLE_PROPERTY, "LR43",
        "A property reads like a field, so it cannot hand back a failure to handle.";
    active 169 => STRING_NOT_INDEXABLE, "LR37",
        "A string is UTF-8, so it is read through its own APIs rather than by index.";
    active 170 => INDEX_TYPE, "LR37",
        "An index has the type the container is keyed by.";
    active 171 => RETURN_TYPE, "LR9.1",
        "A return gives a value of the type its function declares.";
    active 172 => CONSTRAINT_NOT_SATISFIED, "LR19",
        "A type argument satisfies what `where` requires of the parameter it fills.";
    active 173 => INVALID_CAST, "LR33",
        "`as` converts between numeric types; there is no universal cast.";
    active 174 => MIXED_ARITHMETIC, "LR39",
        "Arithmetic is on one numeric type; mixing two means writing the conversion.";
    active 175 => ASSIGN_TO_CONSTANT, "LR5.2",
        "`const` binds a name once, and nothing may bind it again.";
    active 176 => CONST_NOT_EVALUABLE, "LR24",
        "A `const` is worked out while compiling, over the pure subset that allows.";
    active 177 => UNSAFE_REQUIRED, "LR29.2",
        "A low-level operation is written inside an `unsafe` context.";
    active 178 => ADDRESS_OF_TEMPORARY, "LR72",
        "An address is taken of a binding that stays put, not of a value in flight.";
    active 179 => ADDRESS_OF_CONSTANT, "LR72",
        "`&mut` takes a mutable address, which a `const` binding does not have.";
    active 180 => UNINITIALIZED_READ, "LR5.1",
        "A binding declared without a value is written to before it is read.";
    active 181 => STATIC_THROUGH_INSTANCE, "LR42",
        "A static takes no receiver, so it is called through its type.";
    active 182 => OPERATOR_NOT_OVERLOADED, "LR36",
        "An operator on a type it is not built in for calls the protocol method it names.";
    active 183 => CONCAT_OPERANDS, "LR11.2",
        "`..` joins two strings, and nothing is stringified on its way in.";
    active 184 => ARITHMETIC_OPERANDS, "LR11.1",
        "Arithmetic is on numbers of one type.";
    active 185 => BITWISE_OPERANDS, "LR11.5",
        "A bitwise operator is on integers of one type.";
    active 186 => PROTOCOL_RESULT, "LR36",
        "A protocol method returns what the operator calling it needs.";
    active 187 => DERIVE_TARGET, "LR75",
        "`@derive` applies to a declaration with members to write into.";
    active 188 => DERIVE_COLLIDES, "LR75",
        "A derived member does not replace one written by hand.";
    active 189 => DERIVE_UNAVAILABLE, "LR75",
        "A field has the protocol before the type deriving it can be written out.";
    active 190 => FINALIZER_TARGET, "LR51",
        "`@finalizer` applies to an instance function declared by a `ref struct`.";
    active 191 => FINALIZER_SIGNATURE, "LR51",
        "A finalizer takes no explicit parameters, returns `()`, and is not async or generic.";
    active 192 => DUPLICATE_FINALIZER, "LR51",
        "A `ref struct` declares at most one finalizer.";
    active 193 => IDENTITY_REQUIRED, "LR32",
        "`identical` takes values with observable identity.";
}

#[cfg(test)]
mod tests {
    use super::*;

    #[allow(
        dead_code,
        reason = "a fixture table, exercised through lookup and active"
    )]
    mod sample {
        use super::*;

        registry! {
            active  1 => FIRST_RULE,  "LR3.2", "The first rule.";
            retired 2 => SECOND_RULE, "",     "Retired: folded into LR0001.";
            active  9 => THIRD_RULE,  "LR4.3", "The third rule.";
        }
    }

    #[test]
    fn retired_numbers_stay_in_the_table() {
        let entry = sample::lookup(2).expect("retired codes remain addressable");
        assert!(!entry.is_active());
        assert_eq!(entry.code.to_string(), "LR0002");
    }

    #[test]
    fn only_active_rules_are_reported_as_enforced() {
        let names: Vec<_> = sample::active().map(|entry| entry.name).collect();
        assert_eq!(names, ["FIRST_RULE", "THIRD_RULE"]);
    }

    #[test]
    fn lookup_finds_entries_and_misses_gaps() {
        assert_eq!(sample::lookup(1).map(|e| e.spec), Some("LR3.2"));
        assert_eq!(sample::lookup(9).map(|e| e.code), Some(sample::THIRD_RULE));
        assert!(sample::lookup(5).is_none());
    }
}
