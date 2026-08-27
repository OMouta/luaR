# LuaR Language Specification

> Working specification for a compiled, general-purpose language derived from the syntax and ergonomics of Luau.

## 1. Overview

LuaR is a statically compiled, general-purpose programming language inspired by Luau and Lua. It is not a Luau implementation and does not aim for Luau compatibility.

LuaR keeps the parts of Luau that make code concise and readable: lightweight syntax, first-class functions, table-like literals, type inference, structural types, expression-oriented programming, and familiar control flow. It extends that foundation with features intended for general-purpose software development, including native value types, records, enums, pattern matching, decorators, modules, explicit error handling, async programming, interfaces, generics, package-aware imports, and native interoperability.

A conforming implementation compiles source code before execution. LuaR does not define an interpreter execution model.

LuaR is designed around the following properties:

- Familiarity for Lua and Luau programmers.
- Static typing with strong inference.
- Predictable compiled semantics.
- Native data representation where possible.
- Safe defaults without requiring ownership or borrow syntax.
- First-class support for application, library, CLI, server, and systems-adjacent programming.
- Lightweight syntax that remains recognizably descended from Luau.
- Explicit language features instead of relying on metaprogramming tricks for ordinary programming tasks.

---

## 2. Source Files

Source files use UTF-8.

The source file extension is `.luar`.

A source file is a module.

```lua
import { readText } from "std/fs"

export function main(): Result<(), Error>
    local text = readText("./hello.txt")?
    print(text)
    return Result.Ok(())
end
```

Source text is case-sensitive.

Identifiers may contain Unicode letters, but standard-library and public API identifiers should normally use ASCII.

---

## 3. Lexical Structure

### 3.1 Identifiers

Identifiers begin with a letter or `_` and may continue with letters, digits, and `_`.

```lua
name
_user
httpClient
Vec3
```

Conventional casing:

- local variables and functions: `camelCase`
- types, enums, interfaces, and decorators: `PascalCase`
- constants: implementation and library style may choose `UPPER_CASE`
- private names may begin with `_`

Casing is convention, not semantics.

### 3.2 Keywords

The complete set of reserved keywords is:

```text
and         as          async       await       break
case        catch       const       continue    decorator
defer       do          else        elseif      end
enum        export      extend      false       finally
for         from        function    if          implements
import      in          interface   internal    is
local       match       mut         nil         not
or          private     property    public      ref
repeat      return      scope       static      structural
struct      then        throw       true        try
type        typeof      unsafe      until       where
while
```

Reserved but currently unused, rejected rather than treated as identifiers:

```text
comptime    effect      impl        macro       yield
```

Additional reserved words may be added before the first stable release.

### 3.3 Comments

Single-line comments use `--`.

```lua
-- comment
local x = 10
```

Block comments use Luau-style long comments.

```lua
--[[
    block comment
]]
```

Nested block comments are permitted.

### 3.4 Semicolons

Semicolons are optional statement separators.

```lua
local a = 1
local b = 2
```

and

```lua
local a = 1; local b = 2
```

are equivalent.

A formatter should omit semicolons except where needed to disambiguate syntax.

---

## 4. Literals

### 4.1 Nil

`nil` represents the absence of a value.

```lua
local value = nil
```

`nil` is not implicitly assignable to every type. A type must explicitly permit absence.

```lua
local user: User? = nil
```

### 4.2 Booleans

```lua
true
false
```

The type is `bool`.

LuaR has no truthiness. Conditions in `if`, `elseif`, `while`, `until`, and match guards must have type `bool`, and `and`, `or`, and `not` accept only `bool` operands.

```lua
if user ~= nil then     -- correct
if user then            -- compile-time error: User? is not bool
```

Lua's `value or default` idiom is served by `??` (LR8), which tests for `nil` specifically rather than for falsiness.

### 4.3 Integers

Integer literals are integers when their value can be represented as the inferred integer type.

```lua
0
42
-10
1_000_000
0xff
0b1010
0o755
```

Digit separators using `_` are ignored.

The default inferred integer type is `int`. Explicit-width integer types are also available:

```text
i8
i16
i32
i64
u8
u16
u32
u64
```

`int` is exactly `i64` and `uint` is exactly `u64` on every target, including 32-bit and WebAssembly targets. Integer width is not a property of the host machine. Pointer-sized integers, where a program genuinely needs them, use the distinct `isize` and `usize` types, which exist only for FFI and allocator code.

Integer overflow in ordinary arithmetic traps in every compilation mode, including release builds. Overflow behavior does not vary with optimization level, so a program that traps in testing traps in production rather than silently wrapping.

Wrapping, saturating, and checked arithmetic are explicit operations:

```lua
local a = x:wrappingAdd(y)      -- wraps on overflow
local b = x:saturatingAdd(y)    -- clamps to the type's bounds
local c = x:checkedAdd(y)       -- int?, nil on overflow
```

### 4.4 Floating-Point Numbers

```lua
1.0
3.14159
1.5e10
```

The default floating-point type is `float`, defined as IEEE-754 64-bit binary floating point.

Explicit `f32` and `f64` types exist. `float` is an alias of `f64`.

There is no implicit conversion between integers and floating-point values where information may be lost.

### 4.5 Strings

Strings are immutable sequences of UTF-8 bytes and are required to contain valid UTF-8.

```lua
local name = "Jon Doe"
```

Escape sequences include:

```text
\n
\r
\t
\\
\"
\'
\`
\{
\0
\xNN
\u{...}
```

Every delimiter is escapable, so any character can appear in a literal that could otherwise end it: `\"` in a string, `\'` in a character literal (LR6.1), and `` \` `` and `\{` in an interpolated string (LR4.6), where a backtick would close the literal and `{` would open an expression.

`\xNN` writes one byte. A string holds valid UTF-8, so a byte above `\x7f` is written `\u{...}` or belongs in a byte string (LR4.7).

A quoted string ends at the end of its line. An unterminated one is an error at the line it opened on, rather than a literal that runs on to the next quote somewhere later in the file. Values that span lines use long strings:

```lua
local text = [[
hello
world
]]
```

Long strings take no escapes, and may be written at a level, `[==[` closed by `]==]`, so that a string can contain any shorter bracket sequence.

### 4.6 String Interpolation

Interpolated strings use backticks.

```lua
local name = "Jon Doe"
local message = `Hello, {name}!`
```

Any expression may appear inside `{}` if it can be formatted as a string.

```lua
print(`2 + 2 = {2 + 2}`)
```

Interpolation is syntax, not runtime source evaluation.

An interpolated string takes the escapes of LR4.5 and, like a quoted string, ends at the end of its line. A literal backtick or `{` is written `` \` `` or `\{`.

### 4.7 Byte Strings

Byte-oriented data is represented by the standard `bytes` type.

A byte string literal is written:

```lua
b"hello"
```

A byte string is not implicitly convertible to `string`.

---

## 5. Variables and Bindings

### 5.1 Local Bindings

`local` introduces a mutable local binding.

```lua
local count = 0
count += 1
```

The type is inferred from the initializer unless declared explicitly.

```lua
local count: i64 = 0
```

A binding declared with a type takes values of that type. An integer literal takes the declared type when the value is representable in it (LR39).

A local declaration without an initializer requires a type.

```lua
local socket: Socket
```

The compiler must prove that the binding is initialized before it is read.

### 5.2 Immutable Bindings

`const` introduces an immutable binding.

```lua
const port = 8080
```

Reassignment is forbidden.

Immutability applies to the binding, not recursively to referenced objects unless the object's type itself is immutable.

### 5.3 Destructuring

Records, structs, and tuples destructure directly, because their shape is statically known and the binding cannot fail.

```lua
local { name, age } = user
local (x, y) = point
```

Lists do not destructure in a binding, because a list's length is a runtime property and `local [a, b] = values` would have to trap on a short list. Matching a list by shape is a refutable pattern and belongs in `match` (LR16.2).

Renaming uses `as`, matching import renaming (LR21.1).

```lua
local { name as displayName } = user
```

`:` is never a value-binding separator in LuaR. It introduces a type and nothing else (LR89.1).

### 5.4 Assignment Operators

The complete set of compound assignment operators is:

```text
+=   -=   *=   /=   //=   %=   **=
&=   |=   ^=   <<=  >>=
```

There is no `..=`. The token `..=` is the inclusive range operator (LR10.4), so concatenating in place is written out:

```lua
text = text .. suffix
```

Compound assignment evaluates its target exactly once.

---

## 6. Primitive Types

The core primitive types are:

```text
nil
bool

i8 i16 i32 i64
u8 u16 u32 u64
int uint
isize usize

f32 f64
float

string
bytes
char

never
any
unknown
```

### 6.1 `char`

`char` represents a Unicode scalar value.

```lua
local c: char = 'A'
```

Single quotes denote character literals, not strings.

### 6.2 `never`

`never` represents an expression that cannot produce a value.

Examples include an unconditional throw, process termination, and an infinite loop proven not to break.

```lua
function fail(message: string): never
    throw Error(message)
end
```

### 6.3 `unknown`

`unknown` is a type-safe top type.

A value of type `unknown` cannot be used as another type until checked or narrowed.

```lua
function inspect(value: unknown)
    if value is string then
        print(value:upper())
    end
end
```

### 6.4 `any`

`any` disables static type checking for operations involving that value.

It exists primarily for dynamic interoperability, untyped boundaries, migration, and reflective APIs.

```lua
local value: any = foreignValue()
value:whatever().anything
```

Use of `any` should be visible in tooling and may be linted.

`any` is not the default type for unresolved expressions.

---

## 7. Type Inference

LuaR performs local and contextual type inference.

```lua
local count = 10        -- int
local name = "hello"    -- string
local active = true     -- bool
```

Function parameters in exported APIs must have explicit types unless the compiler can encode a stable inferred signature in module metadata and the implementation permits inferred public signatures.

Function return types may be inferred.

```lua
function add(a: int, b: int)
    return a + b
end
```

The inferred return type is `int`.

Type inference must never depend on execution order or profiling information.

---

## 8. Optional Types

`T?` is shorthand for `T | nil`.

```lua
local user: User? = findUser(id)
```

Optional access uses `?.`.

```lua
local city = user?.address?.city
```

If any receiver in an optional chain is `nil`, the complete chain evaluates to `nil`.

Optional indexing is permitted.

```lua
local value = map?[key]
```

The nil-coalescing operator `??` returns the left operand unless it is `nil`.

```lua
local name = user.name ?? "Anonymous"
```

`??` does not treat `false`, `0`, or an empty string as absent.

Optional values must be narrowed before ordinary member access.

```lua
if user ~= nil then
    print(user.name)
end
```

---

## 9. Functions

Functions are first-class values.

### 9.1 Function Declarations

```lua
function add(a: int, b: int): int
    return a + b
end
```

A call passes an argument for every parameter that has no default, and each argument has the type its parameter declares. A parameter list ending in a variadic takes any number of further arguments (LR9.4, LR9.6).

A `return` gives a value of the type the function declares. A function that declares no result returns nothing, and a bare `return` leaves it.

### 9.2 Anonymous Functions

```lua
local double = function(value: int): int
    return value * 2
end
```

Short closures use arrow syntax:

```lua
local double = (value: int) => value * 2
```

Multiple statements require a normal function body.

### 9.3 Function Types

```lua
type Handler = (Request) -> Response
type AsyncHandler = async (Request) -> Response
```

### 9.4 Default Parameters

```lua
function greet(name: string = "world")
    print(`Hello, {name}`)
end
```

Default expressions are evaluated at the call site when the argument is omitted.

They run after the arguments the call writes, in the order their parameters are declared.

### 9.5 Named Arguments

Any parameter may be passed by name using its declared name and `=`.

```lua
connect(
    host = "localhost",
    port = 5432,
    secure = true,
)
```

Named arguments use `=` rather than `:` so that they match record and struct literals, and so that `:` remains reserved for type annotations. Without this rule, `parse(value: string)` would be ambiguous between a named argument and a typed parameter.

Named arguments may be mixed with positional arguments only when positional arguments occur first.

### 9.6 Variadic Parameters

```lua
function printAll(...values: string)
    for value in values do
        print(value)
    end
end
```

Within the function, `values` behaves as a read-only variadic sequence.

### 9.7 Returning Several Values

A function returns exactly one value. Returning several values means returning a tuple (LR14).

```lua
function divide(a: int, b: int): (int, int)
    return (a // b, a % b)
end

local (quotient, remainder) = divide(10, 3)
```

Lua's adjusting multiple-value calling convention does not exist. There is no truncation to one value in expression position, no padding with `nil`, and no difference between `f()` in the middle and at the end of an argument list. A call is one value of one type everywhere it appears.

Parenthesized destructuring is sugar for binding tuple elements, so this is equivalent:

```lua
local result = divide(10, 3)
local quotient = result.0
local remainder = result.1
```

### 9.8 Closures

Closures may capture variables from lexical scope.

```lua
function counter()
    local value = 0

    return function()
        value += 1
        return value
    end
end
```

Captured mutable variables retain shared mutable identity.

---

## 10. Control Flow

### 10.1 If

```lua
if condition then
    work()
elseif otherCondition then
    other()
else
    fallback()
end
```

`if` may also be used as an expression.

```lua
local label = if score >= 50 then "pass" else "fail"
```

All reachable branches of an `if` expression must produce compatible types.

### 10.2 While

```lua
while running do
    tick()
end
```

### 10.3 Repeat

```lua
repeat
    value = read()
until value ~= nil
```

The body runs before the condition is tested, so it always runs at least once.

The condition is part of the body's scope and reads the bindings it declares.

```lua
repeat
    local line = readLine()
until line == nil
```

### 10.4 Ranges

A range is an ordinary value written with an explicit bound marker:

```text
a..<b    exclusive of b
a..=b    inclusive of b
```

```lua
for i in 0..<count do
    print(i)
end

for i in 1..=10 do
    print(i)
end
```

There is no bare `a..b` range. `..` is string concatenation (LR11.2) and only that, so `a .. b`, `a..<b`, and `a..=b` are three distinct tokens with no context-sensitive parsing and no ambiguity against float literals.

There is also no `for i = start, stop do` form. Lua's numeric `for` is inclusive, which composes badly with zero-based indexing (LR37): `for i = 0, values.length` reads naturally and runs one iteration too many. A single loop form over an explicit range removes that class of bug.

```lua
for i in 0..<values.length do
    print(values[i])
end
```

Ranges are values and may be stored, passed, and used for slicing (LR38).

```lua
const window = 10..<20
local page = values[window]
```

A range whose lower bound exceeds its upper bound is empty rather than an error, and iterates zero times. Descending iteration uses an explicit method:

```lua
for i in (0..<count):reversed() do
    print(i)
end
```

### 10.5 Iteration

```lua
for item in items do
    print(item)
end
```

Indexed iteration:

```lua
for index, item in items:enumerated() do
    print(index, item)
end
```

Maps may expose key/value iteration:

```lua
for key, value in map do
    print(key, value)
end
```

Iteration is defined by the iterable protocol rather than by special-casing tables.

### 10.6 Break and Continue

```lua
for item in items do
    if item.invalid then
        continue
    end

    if item.done then
        break
    end
end
```

### 10.7 Labeled Control Flow

Loops may be labeled.

```lua
outer: for row in rows do
    for value in row do
        if value == target then
            break outer
        end
    end
end
```

---

## 11. Operators

### 11.1 Arithmetic

```text
+  -  *  /  //  %  **
```

`/` is floating-point division and always produces a floating-point result. Applying `/` to two integers is a compile-time error, with a diagnostic pointing at `//` and at explicit conversion.

```lua
local ratio = 10 / 3          -- error: / is not defined for (int, int)
local ratio = 10.0 / 3.0      -- 3.333...
local ratio = a as f64 / b as f64
```

`//` is integer division, defined only on integers, truncating toward zero.

```lua
local whole = 10 // 3         -- 3
local whole = -10 // 3        -- -3
```

Division by zero traps for integers. Floating-point division follows IEEE-754.

`%` is the remainder, defined so that `(a // b) * b + (a % b) == a`.

`**` is exponentiation. Lua spells this `^`, which LuaR uses for bitwise XOR (LR11.5).

Silently truncating `10 / 3` to `3` is the kind of lossy implicit behavior LR4.4 rules out for conversions, so it is ruled out here too.

Both operands are numbers of one type (LR39). A type these are not built in for takes them through the protocol each names (LR36).

### 11.2 Concatenation

String concatenation uses `..`.

```lua
local full = first .. last
```

Both operands must already be `string`. There is no implicit stringification; use interpolation (LR4.6) or `Display` (LR35) to convert.

`..` is concatenation in every position. Ranges are spelled `..<` and `..=` (LR10.4) precisely so this operator keeps one meaning.

### 11.3 Comparison

```text
==
~=
<
<=
>
>=
```

Comparison is built in for the primitive types (LR6). Every other type compares through the `Eq` and `Comparable` protocols (LR36).

### 11.4 Logical Operators

```text
and
or
not
```

Operands must have type `bool` and the result has type `bool`. `and` and `or` short-circuit.

They do not return operand values as Lua's do. Value-returning `and`/`or` depends on truthiness, which LuaR does not have (LR4.2), and it defeats narrowing: `local port = config.port or 8080` silently discards a legitimate `0`.

The two Lua idioms it replaces have direct spellings:

```lua
local port = config.port ?? 8080              -- was: config.port or 8080
local label = if ok then "yes" else "no"      -- was: ok and "yes" or "no"
```

### 11.5 Bitwise Operators

```text
&
|
~
^
<<
>>
```

Where `~` is unary bitwise NOT when used with one operand and inequality remains `~=`.

These are defined on integers of one type (LR39). A type they are not built in for takes them through the protocol each names (LR36).

### 11.6 Pipeline Operator

LuaR does not define a pipeline operator. Method chaining and ordinary calls cover its uses, and a second call syntax would not earn its weight.

### 11.7 Precedence and Associativity

Tightest first. Operators on the same row bind equally.

```text
f(x)  x[i]  x.name  x:name()  x?  x?.name        postfix, left
**                                               right
not x   -x   ~x   &x   &mut x                     prefix
as   is                                          left
*   /   //   %                                   left
+   -                                            left
..                                               right
<<   >>                                          left
&                                                left
^                                                left
|                                                left
??                                               right
==   ~=   <   <=   >   >=                        none
and                                              left
or                                               left
..<   ..=                                        none
```

This is Lua's table with LuaR's additions placed in it, so familiar expressions keep their familiar shape. `a & b == c` compares `a & b`, as in Lua, rather than masking with the result of a comparison.

`**` binds tighter than prefix `-`, so `-x ** 2` is `-(x ** 2)`, and it associates to the right, so `2 ** 3 ** 2` is `2 ** (3 ** 2)`.

`as` and `is` bind tighter than arithmetic, so `a as f64 / b as f64` divides the two converted values (LR11.1).

`??` binds tighter than comparison, so `x ?? 0 == y` compares the coalesced value. It associates to the right, so `a ?? b ?? c` tries each in turn.

Comparison and range operators are non-associative. `a < b < c` and `a..<b..<c` are syntax errors rather than expressions that parse one way and mean nothing: the first would compare a `bool` against `c`, and the second has no reading at all.

Ranges bind loosest, so `0..<n + 1` is a range up to `n + 1`.

---

## 12. Records and Structs

LuaR distinguishes dynamic maps from statically laid-out records.

### 12.1 Structural Record Types

A structural record type is declared with `type`.

```lua
type User = {
    id: u64,
    name: string,
    email: string?,
}
```

Record literals use braces.

```lua
local user: User = {
    id = 1,
    name = "Jon Doe",
    email = nil,
}
```

Fields are bound with `=`, consistently with struct literals (LR12.2), map literals (LR13.2), and named arguments (LR9.5).

Structural records are compatible by structure unless marked nominal by another construct.

A record type may be declared with fields omitted from a literal only when those fields are optional. Missing non-optional fields are a compile-time error, not `nil`.

### 12.2 Structs

`struct` defines a nominal, statically laid-out data type.

```lua
struct Vec2
    x: float
    y: float
end
```

Construction:

```lua
local point = Vec2 {
    x = 10.0,
    y = 20.0,
}
```

A literal gives a value for every field the struct declares, and names no field it does not. A field written with a default may be left out.

```lua
struct Request
    path: string
    method: string = "GET"
end

local request = Request { path = "/" }
```

A default is evaluated where the literal is written, after the fields the literal gives, in the order the struct declares them.

Methods may be declared inside the struct.

```lua
struct Vec2
    x: float
    y: float

    function length(self): float
        return math.sqrt(self.x * self.x + self.y * self.y)
    end
end
```

Methods use explicit `self`.

A type declares each member once. Fields, properties, and methods share one namespace, and a method written outside the body (LR20) is the same member as one written inside it. Overloads of one method (LR40) are one member under one name.

Method-call syntax uses `:`.

```lua
point:length()
```

This is syntactic sugar for:

```lua
Vec2.length(point)
```

`self` is an ordinary explicit parameter (LR65), so the desugared form stays valid. It is the same call written out, not a second way to spell it.

`:` calls a method. `.` reaches everything else: fields, properties, tuple elements, static functions, enum variants, and module members.

```lua
point:length()      -- method, receives self
point.x             -- field
rect.area           -- property (LR43)
Vec2.zero()         -- static function, no self
Result.Ok(value)    -- enum variant
math.sqrt(value)    -- module member
```

Writing `point:length()` is a compile-time error whose diagnostic names `:`.

The compiler does not need the distinction. It knows what every member is, and could resolve either spelling. It is kept because it tells a reader whether a call has a receiver, and because it puts the difference between a property and a method at the call site instead of only in the declaration. `rect.area` cannot be a method and `rect:area()` cannot be a property.

### 12.3 Visibility

Members are public by default inside a module when the containing declaration is exported.

A member may be explicitly private:

```lua
struct Client
    private socket: Socket
end
```

A private member is accessible only within the module that declares it. LR44 defines the full set of visibility levels.

### 12.4 Immutable Structs

An immutable struct is declared with `const struct`.

```lua
const struct Point
    x: float
    y: float
end
```

Its fields cannot be mutated after initialization.

---

## 13. Dynamic Maps and Lists

LuaR retains lightweight collection literals but gives them explicit collection types.

### 13.1 Lists

```lua
local names = ["Alice", "Bob", "Charlie"]
```

The inferred type is `List<string>`. `[...]` always produces a sequence and never anything else. With nothing asking for a particular one it is a `List<T>`; where a fixed-size array is called for, it fills that (LR71).

`List<T>` is mutable. Mutability is the common case, and naming the common case `MutableList<T>` taxes every ordinary program to label the unusual one. Immutable collections are separate types with an explicit name (LR59).

Lists are zero-indexed.

```lua
print(names[0])
```

Indexing outside the valid range traps unless a checked accessor is used.

```lua
local name = names:get(index) -- string?
```

### 13.2 Maps

A map literal names its type.

```lua
local scores = Map {
    alice = 10,
    bob = 20,
}
```

Keys that are not identifiers use bracket syntax, and any expression is allowed:

```lua
local headers = Map {
    ["content-type"] = "application/json",
    [statusKey] = "ok",
}
```

The inferred type is `Map<string, int>` and `Map<string, string>` respectively.

A bare `{ ... }` literal is **always** a structural record (LR12.1), never a map. Context does not change what a literal constructs.

```lua
local config = {                -- record: { host: string, mode: string }
    host = "localhost",
    mode = "dev",
}

local config = Map {            -- Map<string, string>
    host = "localhost",
    mode = "dev",
}
```

This costs six characters at the one place a dynamic map is created, and buys a rule with no exceptions: a record has statically known fields with independent types and compile-time member checking, a map has runtime keys with one value type, and which one you get is visible in the source rather than inferred from surrounding context. Reading a literal never requires reading its destination.

`Map<K, V>` is mutable, on the same reasoning as `List<T>`.

### 13.3 Sets

Sets are provided by the standard library.

```lua
local ids = Set { 1, 2, 3 }
```

---

## 14. Tuples

Tuple types use parentheses.

```lua
type Coordinate = (float, float)
```

Values are created with parentheses and at least one comma.

```lua
local point = (10.0, 20.0)
```

`(expression)` with no comma is grouping, not a one-element tuple. The unit tuple is written `()` and is the return type of a function that produces no meaningful value.

Tuples destructure:

```lua
local (x, y) = point
```

Tuple members are also reachable by constant index:

```lua
point.0
point.1
```

The index must be an integer literal, so `point.i` is not valid. Tuple element types are independent, and a runtime index would have no single type.

Tuple types and function types both use parentheses, and are distinguished by `->`:

```lua
type Pair = (int, int)          -- tuple of two ints
type Fn   = (int, int) -> int   -- function taking two ints
```

A parenthesized type list is a tuple unless `->` follows it. In return position `function f(): (int, int)` is therefore a tuple return, and a function-returning function is written `function f(): (int) -> int`.

Tuples are for small, local, positionally obvious groupings. Anything with named meaning should be a record or a struct.

---

## 15. Enums

Enums define nominal tagged values.

### 15.1 Simple Enums

```lua
enum Direction
    North
    South
    East
    West
end
```

### 15.2 Associated Data

```lua
enum Result<T, E>
    Ok(T)
    Err(E)
end
```

Another example:

```lua
enum Message
    Quit
    Move { x: int, y: int }
    Write(string)
end
```

### 15.3 Construction

```lua
local result = Result.Ok(user)
local message = Message.Move { x = 10, y = 20 }
```

Enum variants are namespaced by the enum type.

---

## 16. Pattern Matching

### 16.1 Match Forms

`match` has a statement form, where each case introduces a block:

```lua
match result
    case Result.Ok(value)
        print(value)

    case Result.Err(error)
        log(error)
end
```

A case block extends to the next `case` at the same nesting level or to the closing `end`. Cases do not fall through and need no terminator.

It also has an expression form, where every case is `=> expression`:

```lua
local text = match result
    case Result.Ok(value) => value
    case Result.Err(error) => `error: {error}`
end
```

A single `match` uses one form or the other. Mixing block cases and `=>` cases in the same `match` is a compile-time error, which is what keeps the block form's extent unambiguous.

All cases of an expression `match` must produce compatible types.

### 16.2 Patterns

**Wildcard.** `_` matches anything and binds nothing.

**Binding.** A lowercase identifier matches anything and binds it.

**Literal.** Integer, float, string, char, and boolean literals match by value.

**Enum variant.** With positional or record payload:

```lua
match message
    case Message.Move { x, y }
        moveTo(x, y)

    case Message.Write(text)
        print(text)

    case Message.Quit
        exit()
end
```

**Record and struct.** Fields are matched by name, and `...` allows unlisted fields:

```lua
case User { id = 0, name }
    ...

case User { name, ... }
    ...
```

A field pattern may bind under a different name with `as`:

```lua
case User { name as displayName }
```

**Sequence.** Lists, arrays, and slices match by shape, with at most one rest pattern:

```lua
match args
    case []
        usage()

    case [command]
        run(command)

    case [command, ...rest]
        run(command, rest)
end
```

The rest pattern binds a slice of the remaining elements and may appear at any position:

```lua
case [first, ...middle, last]
    ...
```

**Range.** Ranges match numeric and `char` values:

```lua
case 0..<10
    ...

case 'a'..='z'
    ...
```

**Or-pattern.** `|` combines alternatives, which must bind the same names at the same types:

```lua
case Direction.North | Direction.South
    ...
```

**Type pattern.** `is` matches a member of a union (LR57):

```lua
case value is string
    print(value:upper())
```

Patterns nest freely.

### 16.3 Guards

A guard is a `bool` expression attached to a case:

```lua
case Result.Ok(value) if value > 10
    ...
```

A guarded case is never counted toward exhaustiveness, since the compiler does not evaluate guards.

### 16.4 Exhaustiveness

A `match` over a closed type must cover every possible value. Closed types are enums, booleans, unions of closed types, tuples and records of closed types, and `Result`.

An incomplete match is a compile-time error that lists the uncovered patterns.

Values that are not closed, such as integers, strings, and lists, always require `case _`.

```lua
case _
    ...
```

An unreachable case, one whose patterns are fully covered by earlier cases, is also a compile-time error rather than a warning.

---

## 17. Type Aliases and Unions

### 17.1 Aliases

```lua
type UserId = u64
```

A type alias is not nominally distinct from its target type. It stands for its target everywhere: a value of the target goes wherever the alias is written, and every member the target has, it has.

An alias that stands for itself, directly or around a ring of other aliases, names no type and is an error.

### 17.2 Union Types

```lua
type Id = string | u64
```

A value must be narrowed before operations requiring a particular member type.

```lua
if id is string then
    print(id:upper())
end
```

### 17.3 Intersection Types

Intersection types are supported primarily for structural composition.

```lua
type NamedEntity = Named & Identified
```

An intersection value must satisfy all constituent types.

---

## 18. Interfaces

Interfaces define behavior contracts.

```lua
interface Display
    function display(self): string
end
```

Structs may explicitly implement interfaces.

```lua
struct User implements Display
    name: string

    function display(self): string
        return self.name
    end
end
```

Interfaces may contain properties.

```lua
interface Entity
    id: u64
end
```

Interfaces are nominal at implementation boundaries. A struct does not implement an interface merely because its methods happen to match; it must say `implements`.

Nominal is the default because interface conformance is a claim about behavior, not about spelling. A `Container` with `function draw(self)` should not silently satisfy `Drawable`, and accidental conformance turns an unrelated rename into a breaking change.

An interface may opt into structural conformance when the contract really is just its shape:

```lua
structural interface Readable
    function read(self): bytes
end
```

Any type with a matching `read` satisfies `Readable` without declaring it. This suits narrow, single-method, behavior-obvious protocols, and suits adapting foreign types the author cannot modify.

A `structural interface` may not declare stored properties, since a structural claim over layout has no way to be checked at an API boundary.

### 18.1 Interface Values

An interface value may contain any implementation of that interface.

```lua
function printValue(value: Display)
    print(value:display())
end
```

The exact runtime representation is implementation-defined, but semantics must preserve dynamic dispatch.

---

## 19. Generics

Generic declarations use angle brackets.

```lua
function identity<T>(value: T): T
    return value
end
```

Structs and enums may be generic.

```lua
struct Box<T>
    value: T
end
```

Constraints use `where`.

```lua
function max<T>(a: T, b: T): T
where T: Comparable
    if a > b then
        return a
    end

    return b
end
```

Multiple constraints:

```lua
where T: Hashable & Display
```

Generic specialization strategy is not part of language-level observable semantics. Implementations may monomorphize, share code, or use another representation as long as behavior is preserved.

Generic type parameters are invariant by default unless variance is explicitly supported by the relevant type constructor.

---

## 20. Methods and Extension Methods

Methods may be attached to types in their declaring module.

```lua
function Vec2.normalized(self): Vec2
    local length = self:length()
    return Vec2 {
        x = self.x / length,
        y = self.y / length,
    }
end
```

Extension blocks add statically resolved methods to a type without modifying its declaration. An extension block is named, and is exported and imported like any other declaration.

```lua
-- text/slug.luar
export extend StringSlug for string
    function slug(self): string
        ...
    end
end
```

```lua
import { StringSlug } from "text/slug"

local path = title:slug()
```

Extension methods are only in scope in modules that declare or import the block by name. Importing a module for an unrelated function never silently changes what `text:slug()` means, and a diagnostic for an unknown method can name the extension block to import.

Extension methods:

- do not add stored fields;
- do not alter runtime object layout;
- are resolved statically;
- cannot override existing members;
- are in scope only where their block is declared or imported.

Two imported blocks that define the same method for the same type are a compile-time error at the call site, resolved by naming the block explicitly:

```lua
StringSlug.slug(title)
```

---

## 21. Modules

Every source file is a module.

Declarations are private to the module unless exported.

```lua
function internalHelper()
end

export function publicFunction()
end
```

Types may also be exported.

```lua
export struct Client
    ...
end
```

### 21.1 Imports

Named imports:

```lua
import { Client, Request } from "http"
```

Renamed imports:

```lua
import { Client as HttpClient } from "http"
```

Namespace imports:

```lua
import http from "http"
```

Then:

```lua
http.serve(...)
```

Relative imports:

```lua
import config from "./config"
import { User } from "../models/user"
```

Package imports:

```lua
import { Router } from "some-package/router"
```

### 21.2 Import Semantics

Imports are statically resolved.

A module is initialized at most once per process instance.

Cyclic imports are permitted only when the compiler can establish safe initialization. A cycle that requires reading an uninitialized module-level value is a compile-time error.

### 21.3 Module-Level Code

Module-level expressions are allowed for constant initialization and ordinary initialization.

```lua
const version = "1.0"

local cache = Cache.new()
```

Arbitrary top-level side effects are permitted but discouraged for reusable libraries.

---

## 22. Packages

LuaR defines package-aware import semantics but does not require a specific registry.

A package may contain:

- source modules;
- native libraries;
- resources;
- generated code;
- package metadata.

Package identity consists of a package name and resolved version/source identity.

Two independently resolved versions of the same package may coexist when the package system supports it.

LuaR does not expose registry-specific syntax.

---

## 23. Decorators

Decorators attach compile-time metadata or invoke compile-time transformation hooks under controlled language rules.

Syntax:

```lua
@deprecated("Use newApi instead")
function oldApi()
end
```

Decorators may be applied to supported declarations:

```lua
@serializable
struct User
    id: u64
    name: string
end
```

Arguments must be compile-time evaluable unless a decorator explicitly accepts symbolic references.

```lua
@route("/users/:id")
@auth(role = "admin")
async function getUser(id: string): Result<User, HttpError>
    ...
end
```

### 23.1 Decorator Semantics

A decorator is not an arbitrary runtime function call.

Decorators operate in a restricted compile-time environment.

A decorator may only affect the declaration it is attached to. Specifically, it may:

- inspect that declaration;
- attach metadata to it;
- validate its shape;
- add members to it;
- add interface implementations for it;
- alter compiler-recognized attributes on it;
- produce diagnostics.

A decorator may **not** introduce new top-level declarations. `@derive(Json)` on `struct User` may add a `Serialize` implementation for `User`; it may not also declare a `UserBuilder` struct or a free function.

This is the boundary that keeps the language readable by reading it. If decorators could emit arbitrary declarations, then a name in a module might come from no visible source, and every tool from grep to go-to-definition would need to run the compiler's expansion phase to answer where a symbol is defined. Restricted to their target, decorators can still express serialization, equality, routing, ORM mapping, and dependency registration, and every name in a module still traces back to something written in it.

A decorator may not read or write unrelated modules.

Decorators are expanded before final type checking of generated declarations.

Decorator expansion must be deterministic for a fixed compiler environment and package graph.

### 23.2 Built-In Attributes

LuaR reserves built-in decorators for ABI and compiler semantics.

Examples:

```lua
@inline
@noinline
@deprecated
@cold
@repr("C")
@test
```

Compiler-specific decorators must use a namespaced form rather than polluting ordinary source syntax.

---

## 24. Compile-Time Evaluation

LuaR supports restricted compile-time expressions.

```lua
const bufferSize = 1024 * 64
```

`const` initializers must be compile-time evaluable when their value is required by type layout, decorators, array sizes, or other compile-time contexts.

Compile-time evaluation is limited to two places:

1. `const` initializers, evaluated over a pure subset of the language: literals, arithmetic and comparison, string operations, tuple/record/array construction, enum construction, and calls to other `const` values.
2. The decorator API (LR23), which runs in the compiler and is the mechanism for generated code.

There is no user-facing `comptime` block. `comptime` remains reserved (LR81) and a compiler rejects it rather than treating it as an identifier.

Exposing general compile-time execution would give LuaR a second, differently-scoped language inside itself, with its own rules about what is available, its own failure modes, and its own effect on build reproducibility and IDE responsiveness. Decorators already cover the cases that motivate it, in a form that is typed, bounded to a target, and inspectable.

Compile-time evaluation, in either place, has no access to the network, environment variables, filesystem, clock, randomness, or process state. Compilation of a fixed source tree and package graph is reproducible.

LuaR does not define a textual macro system.

---

## 25. Errors

LuaR distinguishes recoverable errors from unrecoverable program faults.

### 25.1 `Result`

Recoverable failures should normally use `Result<T, E>`.

```lua
function readConfig(path: string): Result<Config, IoError>
    ...
end
```

### 25.2 Propagation Operator

`?` propagates the error branch of a `Result`, and nothing else.

```lua
function loadUser(path: string): Result<User, Error>
    local text = fs.readText(path)?
    local user = json.decode<User>(text)?
    return Result.Ok(user)
end
```

`expression?` requires that the enclosing function returns `Result<_, E>`, and that the expression's error type converts into `E` through `Into` (LR35). On `Err`, it returns from the function; on `Ok`, it evaluates to the wrapped value.

`?` does **not** apply to optionals. One operator that propagates errors in some positions and absence in others would mean the reader has to know the enclosing function's return type to know what `x?` does, and `Result<T?, E>` would be genuinely ambiguous.

An optional becomes a `Result` explicitly:

```lua
function loadUser(id: u64): Result<User, Error>
    local user = findUser(id):okOr(Error(`user {id} was not found`))?
    return Result.Ok(user)
end
```

Optionals have their own tools: `?.` for chaining, `??` for defaults, `~= nil` for narrowing, and `match` for exhaustive handling. They do not need a propagation operator.

### 25.3 Exceptions

LuaR also supports exceptions for exceptional control flow and foreign APIs.

```lua
throw Error("connection lost")
```

Catching:

```lua
try
    risky()
catch error: NetworkError
    recover(error)
catch error
    log(error)
finally
    cleanup()
end
```

A `throw` expression has type `never`.

Exceptions are unchecked. They do not appear in function signatures, and the compiler does not verify that they are caught. Making them checked would reproduce Java's checked-exception problem, where every signature accumulates the failure modes of everything it transitively calls; making them silent but common would defeat the point of `Result`.

The role of each mechanism is fixed:

- `Result` is for failures the caller is expected to handle. Every fallible standard-library API returns `Result`. Public APIs should do the same.
- Exceptions are for exceptional control flow, chiefly foreign boundaries that already unwind and cross-cutting aborts such as a request deadline.
- `panic` is for violated invariants.

A public API that throws for an expected failure, such as a missing file or malformed input, is a design error that tooling should flag.

An exception escaping `main` reports the error and exits unsuccessfully.

### 25.4 Panic

`panic(message)` terminates the current program or task according to runtime policy and is not recoverable through ordinary `catch`.

Panics represent violated invariants, impossible states, bounds errors, failed assertions, and similar faults.

---

## 26. Defer

`defer` schedules code to execute when the current scope exits.

```lua
local file = File.open(path)?
defer file:close()

process(file)
```

Deferred expressions execute in reverse order of registration.

The expression is evaluated where the scope exits, not where the `defer` is written. It reads whatever the bindings it names hold at that point.

They execute when leaving scope through:

- normal completion;
- `return`;
- `break`;
- `continue`;
- exception unwinding.

Whether they run during process-aborting panics is implementation-defined unless the runtime guarantees unwinding.

A deferred operation must not replace an already propagating error without explicit handling.

---

## 27. Async Functions

Async functions use `async`.

```lua
async function fetchUser(id: u64): Result<User, Error>
    local response = await http.get(`/users/{id}`)
    return decodeUser(response.body)
end
```

Calling an async function returns a `Task<T>`.

```lua
local task: Task<Result<User, Error>> = fetchUser(1)
```

`await` suspends the current async task until completion.

`await` may only appear in an async context unless a dedicated top-level async entrypoint is supported.

### 27.1 Async Entry Point

A program may define:

```lua
export async function main(): Result<(), Error>
    ...
end
```

The runtime executes the returned task to completion.

### 27.2 Structured Concurrency

The standard concurrency model favors structured task lifetimes.

```lua
async scope tasks
    local a = tasks:spawn(fetchA())
    local b = tasks:spawn(fetchB())

    local resultA = await a
    local resultB = await b
end
```

Tasks created inside a structured scope must finish or be cancelled before the scope exits.

Detached tasks require an explicit API.

### 27.3 Cancellation

Cancellation is cooperative.

Cancellation propagates through structured task relationships unless explicitly shielded.

Resource cleanup through `defer` occurs during ordinary cancellation unwinding.

---

## 28. Threads and Shared State

LuaR permits native threads through the standard library.

Ordinary heap objects are not automatically safe for concurrent mutation.

Types may implement marker interfaces such as:

```text
Send
Sync
```

or equivalent language-defined traits controlling whether values can cross thread boundaries or be shared.

The exact names are subject to standard-library design, but compile-time concurrency checking should prevent obviously unsafe transfers where the type system can express the constraint.

Synchronization primitives include standard abstractions such as:

- mutexes;
- read/write locks;
- channels;
- atomics;
- condition variables;
- semaphores.

LuaR does not expose unsynchronized data races as defined behavior.

---

## 29. Memory Model

LuaR uses automatic memory management for ordinary managed objects.

Programmers do not manually free managed memory.

Value-like structs may live inline, on the stack, in registers, or within other objects according to escape analysis and ABI requirements.

Reference-like data such as strings, lists, maps, closures, interface objects, and heap-promoted values use managed storage.

The exact garbage-collection algorithm is not part of source-level semantics.

### 29.1 References

LuaR does not expose arbitrary pointer arithmetic in safe code.

References preserve object identity where identity is semantically relevant.

### 29.2 Unsafe Code

Low-level operations require an explicit `unsafe` context.

```lua
unsafe
    ...
end
```

Unsafe capabilities may include:

- raw pointers;
- pointer arithmetic;
- unchecked indexing;
- native memory access;
- foreign-layout reinterpretation;
- unchecked casts.

Unsafe code does not disable type checking outside the operations explicitly defined as unsafe.

---

## 30. Ownership and Resource Lifetime

LuaR does not use a Rust-style borrow checker for ordinary programming.

Memory lifetime is automatic.

External resources such as files, sockets, locks, database transactions, and native handles use explicit close/dispose operations with `defer` or scoped APIs.

```lua
local file = File.open(path)?
defer file:close()
```

Types may define deterministic cleanup protocols for use by scoped standard-library helpers, but garbage collection must not be relied upon for timely release of scarce external resources.

---

## 31. Reference Types

There is no `class` construct and no implementation inheritance. Domain modeling uses structs, interfaces, enums, composition, extension methods, and closures.

A `struct` has value semantics: assigning it may copy it, and two structs with equal fields are indistinguishable.

Some types genuinely need reference semantics, where every holder observes one shared, mutable, identifiable object. Connection pools, caches, event buses, and scene nodes are the usual examples, and modeling them as value structs produces silent copies of state that was meant to be shared. These are declared `ref struct`:

```lua
ref struct Counter
    value: int = 0

    function increment(self)
        self.value += 1
    end
end

local a = Counter {}
local b = a
b:increment()
print(a.value)      -- 1
```

A `ref struct`:

- is always heap-allocated and managed;
- is copied by reference, so all bindings observe one object;
- has observable identity (LR32);
- may declare a finalizer (LR51);
- may be self-referential and cyclic;
- may not also be declared `const struct`.

`ref struct` is a modifier on an existing construct rather than a separate declaration form, so reference types gain no additional powers. In particular they still do not inherit. A reference type composes and implements interfaces exactly as a value struct does:

```lua
struct Client
    transport: Transport

    async function send(self, request: Request): Result<Response, Error>
        return await self.transport:send(request)
    end
end
```

---

## 32. Equality and Identity

`==` performs semantic equality.

Primitive value types compare by value.

Structs may derive equality when all fields are comparable.

```lua
@derive(Eq)
struct Point
    x: int
    y: int
end
```

`is` performs runtime type tests only:

```lua
if value is string then
```

It never tests identity. One operator meaning "same object" with a value on the right and "is of this type" with a type on the right requires the reader to resolve whether a name is a type or a binding before knowing what the line does, and it breaks outright for a binding that shadows a type name.

Reference identity is a standard-library function:

```lua
import { identical } from "std/mem"

if identical(a, b) then
```

`identical` accepts only types with observable identity: `ref struct` types (LR31), closures, interface values, and the standard reference-backed collections. Calling it on value structs, strings, or primitives is a compile-time error rather than an answer that depends on whether the compiler happened to intern or copy the value.

Identity is therefore a property a type declares, not a property every value happens to have. This leaves the compiler free to copy, inline, unbox, and intern value types without changing observable behavior.

---

## 33. Casting and Conversion

Safe type conversion uses `as`.

```lua
local value = integer as f64
```

Conversions that may fail return an optional or result depending on the target API.

```lua
local id = text:parse<u64>()?
```

Unchecked representation casts require `unsafe`.

There is no universal C-style cast operator.

Every numeric conversion requires explicit syntax, narrowing or not (LR39).

---

## 34. Reflection

Runtime reflection is intentionally limited.

LuaR provides enough reflection for serialization, dependency injection, tooling, and framework use without requiring every type to carry full metadata.

Types opt into runtime reflection with a decorator:

```lua
@reflect
struct User
    id: u64
    name: string
end
```

A decorator is the right mechanism because reflection is metadata rather than behavior. An interface would imply members the type does not have and would let reflectability be required by a signature; a dedicated modifier would add grammar for what `@derive` and `@repr` already express. `@reflect` also composes: `@derive(Json)` can request it implicitly for the type it is applied to.

Types without `@reflect` carry no field metadata at runtime, and reflecting over them fails at compile time rather than returning an empty description.

Compile-time decorators may inspect richer type metadata than is retained at runtime.

A `typeOf(value)` operation returns runtime type metadata only when that metadata exists.

Static type queries use:

```lua
typeof(expression)
```

`typeof` is evaluated by the compiler.

---

## 35. Standard Protocols

Language syntax desugars to standardized protocols where appropriate.

Examples may include:

```text
Iterator<T>
Iterable<T>
Display
Hash
Eq
Comparable
Index<K, V>
Into<T>
```

The exact standard protocol names are library specification concerns, but user-defined types must be able to participate in ordinary language constructs without compiler-specific hardcoding.

For example, `for value in collection` should work with any conforming iterable.

---

## 36. Operator Overloading

Operator overloading is permitted only through well-defined interfaces.

A user type cannot define arbitrary parser-level operators.

Each overloadable operator names a protocol (LR35) and the method it calls. A type participates by having that method, reached the way any other method is (LR76).

```text
-a          Neg          a:neg()
~a          BitNot       a:bitNot()
a + b       Add          a:add(b)
a - b       Sub          a:sub(b)
a * b       Mul          a:mul(b)
a / b       Div          a:div(b)
a % b       Rem          a:rem(b)
a ** b      Pow          a:pow(b)
a & b       BitAnd       a:bitAnd(b)
a | b       BitOr        a:bitOr(b)
a ^ b       BitXor       a:bitXor(b)
a << b      Shl          a:shl(b)
a >> b      Shr          a:shr(b)
a == b      Eq           a:eq(b)
a[index]    Index        a:index(index)
```

`~=` is the negation of `==` and calls the same method. `<`, `<=`, `>`, and `>=` call `Comparable`, whose `compare(self, other)` returns an `int` that is negative, zero, or positive:

```text
a < b   ->  a:compare(b) < 0
a >= b  ->  a:compare(b) >= 0
```

One method behind four operators is what stops a type reporting `a < b` and `a >= b` both true.

Dispatch is on the left operand, and neither operand is converted first. `a + b` looks for `add` on the type of `a`, and `b` must fit the parameter that method declares. A type that wants both `Vec2 * f64` and `f64 * Vec2` declares the second on `f64` in an extension block (LR20).

An arithmetic, bitwise, or index operator produces whatever its method returns. `==`, `~=`, `<`, `<=`, `>`, and `>=` produce `bool` whatever their method returns, so the protocol pins that method down: `eq` returns `bool` and `compare` returns `int`. A method returning anything else does not implement the protocol, and an operator that would call it is an error.

A compound assignment overloads through the operator it contains, so `a += b` calls `add` (LR5.4).

These operators are not overloadable:

- `and`, `or`, and `not`, which take `bool` and short-circuit (LR11.4).
- `..`, whose operands are already `string` (LR11.2).
- `//`, which is integer division (LR11.1).
- Assignment, `?`, `await`, and member access.

Overloads must not change evaluation order or short-circuit semantics.

---

## 37. Indexing

Lists, strings, bytes, and other sequence APIs are zero-indexed.

```lua
local first = values[0]
```

Strings are UTF-8 and therefore integer indexing does not return a Unicode character in constant time.

Direct indexing a string by integer is not supported.

Use explicit APIs:

```lua
text:bytes()        -- Iterator<u8>
text:chars()        -- Iterator<char>
text:graphemes()    -- Iterator<string>
```

This avoids pretending that UTF-8 strings are arrays of characters. `text.length` is not defined for the same reason; the count you want is `text.byteLength`, `text:chars():count()`, or `text:graphemes():count()`, and they differ.

Strings are not sliced with `[]` either (LR38).

---

## 38. Slices and Ranges

Slicing uses range values (LR10.4).

```lua
local firstTen = values[0..<10]
local window   = values[start..=stop]
```

A range that exceeds the collection's bounds panics, exactly as scalar indexing does. `values:slice(range)` returns `Slice<T>?` for the checked form.

Open-ended ranges are written by omitting a bound:

```lua
values[..<10]
values[10..]
```

A slice of a list is a view rather than a copy. `Slice<T>` borrows its backing storage, and mutating the list while a slice of it is live is a compile-time error where the compiler can see it and a panic where it cannot.

Strings are not sliced with `[]`, on the same reasoning as LR37: a byte range is not a meaningful unit of text, and `text[0..<10]` invites treating one for the other. String subranges come from explicit APIs that name their unit and their failure mode:

```lua
text:byteSlice(0..<10)      -- Result<string, Utf8Error>, errors off a boundary
text:chars():take(10)       -- ten Unicode scalar values
text:graphemes():take(10)   -- ten user-perceived characters
```

---

## 39. Numeric Semantics

Numeric types are not all collapsed into one generic `number`.

```lua
local count: i32 = 10
local size: u64 = 2048
local ratio: f64 = 0.5
```

LuaR provides explicit conversions.

```lua
local ratio = count as f64
```

There is no implicit promotion between numeric types, lossless or otherwise. Arithmetic is on one type, and mixing two means writing the conversion (LR33).

```lua
local total = count as i64 + size
```

A promotion that happens on its own would have to be defined width by width and signedness by signedness, and every reader would have to know that table to know what a line does. Writing it down costs one `as` and reads the same to everyone.

Compile-time integer literals are polymorphic within representable bounds.

```lua
local x: u8 = 10
local y: i64 = 10
```

The literal `10` itself is not forced to one machine representation before contextual typing.

---

## 40. Function Overloading

Named functions may be overloaded when signatures are statically distinguishable.

```lua
function parse(value: string): Document
    ...
end

function parse(value: bytes): Document
    ...
end
```

Overload resolution is compile-time only.

Return type alone cannot distinguish overloads. Two overloads are distinguishable when their parameter lists differ, by holding a different number of parameters or a different type in some position. Two that differ only in their result, or not at all, are an error at the second one.

A call resolves to exactly one overload. Matching none and matching more than one are both errors at the call.

Methods overload on the same terms, and overloads of one method are one member of the type (LR12.2).

Libraries should avoid large overload sets when generics or distinct names are clearer.

---

## 41. Namespaces

Modules are the primary namespace mechanism.

Types provide their own namespace for static members and variants.

```lua
Result.Ok(value)
Path.fromString(text)
```

LuaR does not provide an independent `namespace` declaration.

---

## 42. Static Members

Structs and types may define static functions.

```lua
struct Vec2
    x: float
    y: float

    static function zero(): Vec2
        return Vec2 { x = 0.0, y = 0.0 }
    end
end
```

Called as:

```lua
local origin = Vec2.zero()
```

Static stored fields are module-level storage scoped to the type and must obey module initialization rules.

---

## 43. Properties

Computed properties may be declared where they improve API clarity.

```lua
struct Rectangle
    width: float
    height: float

    property area: float
        get
            return self.width * self.height
        end
    end
end
```

Property access:

```lua
print(rect.area)
```

Properties must behave like field access from the caller's syntax but may execute code.

Properties are part of the core language rather than a library pattern for one reason: without them, turning a stored field into a computed value is a breaking API change, so library authors defensively wrap every field in `getX()` accessors and callers read `user:getName()` forever. With them, `rect.area` can start as a stored field and become computed without touching a caller.

To keep that from becoming a license for hidden work, a property:

- must not be observably fallible, which means its type is not a `Result` (LR25.1), and should not panic;
- must be cheap enough that callers can treat it as field access;
- must be idempotent, returning the same value for unchanged inputs;
- must not be `async`.

Anything that performs I/O, allocates significantly, or can fail is a method, and reads like one at the call site.

Setters are explicit:

```lua
property value: int
    get
        return self.inner
    end

    set(newValue)
        self.inner = newValue
    end
end
```

The property and method distinction is visible at every call site, because properties are reached with `.` and methods with `:` (LR12.2). `rect.area` cannot be a method and `rect:area()` cannot be a property.

Tooling distinguishes computed properties from stored fields, and documentation output marks properties as computed.

---

## 44. Visibility and API Boundaries

Supported visibility levels:

```text
private
internal
public
```

A declaration is private to its module unless it is exported (LR21). `export` is what controls the module surface, and a visibility level never widens it.

The levels apply to the members of a declaration (LR12.3), which are public by default.

`private` narrows a member to the module that declares it.

```lua
export struct Parser
    private state: ParserState
end
```

`internal` narrows a member to the package that declares it, so a dependent package cannot reach it (LR22). Within one package it reads the same as `public`.

`public` may be written where explicit visibility improves readability.

---

## 45. Entrypoints

Executable programs define a module exporting `main`.

Valid forms include:

```lua
export function main()
end
```

```lua
export function main(args: List<string>): int
    return 0
end
```

```lua
export async function main(): Result<(), Error>
end
```

The exact accepted signatures are standardized.

Returning an integer maps to the process exit code.

Returning an error from a `Result` entrypoint prints or reports the error according to runtime conventions and exits unsuccessfully unless the application handles it itself.

---

## 46. Foreign Function Interface

LuaR supports calling native C-compatible APIs.

```lua
@extern("c")
unsafe function puts(text: *const u8): i32
```

A foreign declaration is its own declaration form. It carries a signature and no body, and therefore no `end`. It requires both an explicit ABI annotation and the `unsafe` modifier, since the compiler cannot verify anything about the callee.

Calling one requires an `unsafe` context:

```lua
unsafe
    puts(pointer)
end
```

Foreign declarations may appear at module level only, and their parameter and return types must be ABI-representable: primitives, pointers, and `@repr("C")` types.

C-compatible struct layout uses:

```lua
@repr("C")
struct NativePoint
    x: i32
    y: i32
end
```

Raw pointers and direct FFI interaction are unsafe.

Higher-level safe wrappers should isolate unsafe code.

Native libraries may expose language-native APIs through generated or handwritten bindings.

---

## 47. WebAssembly

WebAssembly is a valid compilation target, but WebAssembly-specific restrictions are target concerns rather than core source-language semantics.

Target capabilities such as filesystem, sockets, threads, and processes depend on the selected runtime environment.

Portable code should query or declare required capabilities through package/build metadata rather than conditional behavior hidden in ordinary expressions.

---

## 48. Conditional Compilation

Compile-time target checks use a restricted condition syntax.

```lua
#if target.os == "windows"
    ...
#elseif target.os == "macos"
    ...
#else
    ...
#end
```

Conditional compilation should be used sparingly.

Feature declarations belong to package/build metadata rather than arbitrary environment variables.

Conditions may test:

- operating system;
- architecture;
- target family;
- enabled package features;
- debug/release mode;
- compiler-defined capabilities.

---

## 49. Assertions

```lua
assert(condition)
assert(condition, "message")
```

Assertions that fail panic.

Debug-only assertions may use:

```lua
debugAssert(condition)
```

Whether debug assertions are included is controlled by compilation mode.

Assertions must not be used where their side effects are required for correct program behavior.

---

## 50. Unreachable Code

The built-in:

```lua
unreachable()
```

has type `never` and indicates that execution reaching that point violates program invariants.

The optimizer may assume it cannot return.

Incorrect use can cause a panic or trap, but not memory unsafety in otherwise safe code.

An unsafe unchecked-unreachable primitive, if provided, must be separately named and restricted to unsafe contexts.

---

## 51. Destructors and Finalization

Managed objects do not have deterministic destructors tied to lexical scope.

A type may define a finalizer for last-resort cleanup of managed resources, but:

- finalization timing is unspecified;
- finalizers may never run at process termination;
- finalizers must not be required for program correctness;
- external resources should use explicit cleanup and `defer`.

This keeps memory management automatic without pretending garbage collection provides deterministic resource lifetime.

---

## 52. Global State

Implicit global variable creation is forbidden.

This is invalid:

```lua
count = 10
```

unless `count` is already declared in scope.

Module-level variables must be declared explicitly.

```lua
local count = 10
```

Mutable module state cannot be exported. `export` applies to functions, types, interfaces, extension blocks, and `const` values only.

```lua
export const defaultTimeout = 30            -- allowed
export local currentMode = "development"    -- compile-time error
```

Exported mutable state makes any module a hidden input to any other, defeats the initialization-order rules in LR78, and cannot be made thread-safe by a caller who can only see the name.

A module that owns mutable state exposes it through functions, which gives the owning module a place to put validation, synchronization, and invariants:

```lua
local currentMode = "development"

export function mode(): string
    return currentMode
end

export function setMode(value: string)
    currentMode = value
end
```

---

## 53. Shadowing

Local variable shadowing is allowed.

```lua
local value = getValue()

if value ~= nil then
    local value = transform(value)
    use(value)
end
```

Tooling may warn about suspicious accidental shadowing.

Parameters may not be redeclared in the same lexical scope.

---

## 54. Scope

LuaR uses lexical scope.

Blocks introduce scopes where declarations occur.

```lua
if condition then
    local value = 10
end

-- value is not visible here
```

Loop variables are scoped to the loop.

Captured values follow closure semantics.

### 54.1 Predeclared Names

A closed set of names is in scope in every module without an import:

```text
print
assert
debugAssert
panic
unreachable
Result
```

Predeclared names occupy a scope outside the module. A declaration or an import of the same name shadows one, and shadowing one is not an error:

```lua
local print = collect
```

Predeclared names are not a module. They cannot be imported from, renamed, or re-exported. Everything else the standard library provides is imported like any other module (LR21.1, LR60).

Type names work the same way. The primitive types (LR6) need no import, and neither do the collection types the language builds from its own literal syntax (LR13, LR59):

```text
List
Map
Set
FrozenList
FrozenMap
FrozenSet
```

Every other name in a type is declared by the module or imported (LR21.1). The standard protocols (LR35) are library names and are imported like any other.

The set is closed. A name belongs in it only because it cannot be written as an ordinary declaration, or because every program needs it to state a signature. `assert` and `debugAssert` depend on compilation mode (LR49), `unreachable` has type `never` (LR50), and `panic` does not return (LR25.4). `Result` names the type of every fallible signature (LR25.1). `print` is neither, and is predeclared so that writing a line of output does not require an import.

---

## 55. Evaluation Order

Expression evaluation order is left-to-right unless a construct explicitly defines otherwise.

Function arguments are evaluated left-to-right.

```lua
foo(a(), b(), c())
```

calls `a`, then `b`, then `c`, then `foo`.

Record literal field initializers are evaluated in source order.

An assignment evaluates its target before its value.

```lua
values[index()] = compute()
```

calls `index`, then `compute`.

A compound assignment evaluates its target once, and reads and writes that one place.

Optimizations must preserve observable evaluation order.

---

## 56. Short-Circuiting

`and`, `or`, `??`, optional chaining, and propagation operators short-circuit.

```lua
if value ~= nil and isValid(value) then
```

does not evaluate `isValid(value)` when `value` is `nil`, and the narrowing from the left operand is in effect in the right one.

```lua
value ?? fallback()
```

does not evaluate `fallback()` when `value` is not `nil`.

---

## 57. Type Narrowing

Control-flow analysis narrows types.

```lua
function printValue(value: string | int)
    if value is string then
        print(value:upper())
    else
        print(value + 1)
    end
end
```

Nil checks narrow optionals.

```lua
if user ~= nil then
    print(user.name)
end
```

Pattern matching narrows enum and union variants.

Narrowing is invalidated when mutation or aliasing can make the assumption unsafe.

---

## 58. Never-Initialized and Moved State

Ordinary assignments do not move values by default.

```lua
local a = value
local b = a
```

For small value types this may compile to a copy.

For managed reference types both bindings may refer to the same managed object.

Specific unique resource types may expose move-only semantics if necessary, but move-only behavior must be explicit in the type system rather than inferred unpredictably.

---

## 59. Mutability

Bindings and values have separate mutability.

```lua
const user = User { ... }
```

prevents rebinding `user`, but does not necessarily make `user` deeply immutable.

Immutable data types encode immutability in their type or declaration: `const struct` (LR12.4) for values, and frozen collections for containers.

The standard collections are mutable, and the frozen ones carry the qualifier:

```text
List<T>         Map<K, V>         Set<T>
FrozenList<T>   FrozenMap<K, V>   FrozenSet<T>
```

Naming runs this way round rather than `List`/`MutableList` because mutable collections are what most code builds and returns, and a scheme that makes the common case the longer name gets worked around rather than followed.

Freezing is explicit and one-way, and returns a distinct type rather than a flag on the same one:

```lua
local names = ["Alice", "Bob"]
const roster = names:frozen()   -- FrozenList<string>
```

A frozen collection has no mutating methods at all, so immutability is enforced by the type checker rather than by a runtime error on write. `FrozenList<T>` is accepted anywhere a read-only sequence is expected, and `List<T>` is not implicitly convertible to it.

Fields hold whichever type their invariants require. A struct that must not have its contents changed after construction declares `FrozenList<T>`, and the compiler enforces it without a defensive copy.

---

## 60. Standard Library Expectations

The LuaR standard environment should support general-purpose programming directly.

Core areas include:

```text
std/fs
std/io
std/path
std/process
std/env
std/net
std/http
std/time
std/json
std/encoding
std/crypto
std/thread
std/sync
std/collections
std/mem
std/math
std/random
std/testing
std/log
```

Not every high-level protocol must live in the minimal runtime, but ordinary application programming must not depend on Roblox-like host APIs.

The standard library should prefer typed APIs over loosely structured map-based configuration.

---

## 61. Testing

Test declarations may use a built-in decorator.

```lua
@test
function additionWorks()
    assert(2 + 2 == 4)
end
```

Async tests are permitted.

```lua
@test
async function serverResponds()
    local response = await request(...)
    assert(response.status == 200)
end
```

Parameterized testing belongs to the testing library rather than requiring special core syntax.

---

## 62. Documentation Comments

Documentation comments use `---`.

```lua
--- Returns the user with the given ID.
---
--- Returns `nil` when no matching user exists.
export function findUser(id: u64): User?
    ...
end
```

Documentation comments are retained in compiler metadata where appropriate and exposed to documentation tooling.

Structured tags may be supported but ordinary Markdown is the default documentation format.

---

## 63. Attributes Versus Documentation

Semantic metadata uses decorators.

Human-facing API explanation uses documentation comments.

These are intentionally separate.

```lua
@deprecated("Use connect instead")
--- Opens a connection using the legacy transport.
export function open()
end
```

---

## 64. Formatting

LuaR has one canonical formatter.

The formatter owns whitespace and layout but does not change semantics.

Preferred style:

```lua
function example(value: int): string
    if value > 10 then
        return `large: {value}`
    end

    return `small: {value}`
end
```

Trailing commas are allowed in multiline constructs.

```lua
local user = User {
    id = 1,
    name = "Jon Doe",
}
```

The formatter should preserve comments.

---

## 65. Semantics of `self`

`self` is not an implicit hidden variable outside method syntax.

A method declaration explicitly includes it:

```lua
function length(self): float
```

The compiler infers or validates its type from the containing declaration.

Static methods omit `self`.

This avoids the ambiguity of magic implicit receivers while retaining compact method-call syntax.

`Self` is that same type written down, usable anywhere a type is, inside a `struct`, an `enum`, an `interface`, or an `extend` block:

```lua
interface Comparable
    function compare(self, other: Self): int
end
```

In a generic declaration `Self` carries the declaration's own parameters, so inside `struct Box<T>` it means `Box<T>`.

`Self` is what lets an interface name the implementing type, which is the difference between a protocol every type implements against itself and one that must be given a type argument to say so (LR35).

---

## 66. Constructors

There is no mandatory constructor method.

Struct literals are the default construction mechanism.

```lua
local user = User {
    id = 1,
    name = "Jon Doe",
}
```

Types may expose named constructors:

```lua
struct User
    id: u64
    name: string

    static function new(name: string): User
        return User {
            id = nextId(),
            name = name,
        }
    end
end
```

Then:

```lua
local user = User.new("Jon Doe")
```

This keeps construction explicit and avoids special behavior hidden behind one magic method name.

---

## 67. Dynamic Member Access

Safe statically typed code requires known members.

```lua
user.name
```

Accessing a member by runtime string requires reflection or a dynamic type.

```lua
local object: any = getDynamicObject()
local value = object[key]
```

Structural records are not automatically dynamic dictionaries.

This distinction allows records to have predictable layouts and compile-time member checking.

---

## 68. Metaprogramming

LuaR does not expose Lua metatables as its universal object model.

Ordinary behavior uses explicit features:

- methods;
- interfaces;
- operator protocols;
- decorators;
- reflection;
- extension methods.

Dynamic proxy objects may exist in libraries through dedicated runtime interfaces, but fundamental language behavior should not depend on mutable metatable state.

---

## 69. Nil and Missing Keys

A missing key in a dynamic map returns `nil` through its safe lookup API.

```lua
local value = map:get(key)
```

Direct indexing semantics are type-specific.

Indexing a `Map<K, V>` returns `V?`, so a missing key is a value the type system forces the caller to handle:

```lua
local value: User? = users[id]
```

Indexing a `List<T>` returns `T` and panics out of range (LR70). The difference is deliberate: a missing map key is an ordinary outcome, while an out-of-range list index is a bug in the caller's arithmetic.

For records and structs, an unknown field is a compile-time error rather than `nil`.

This removes a major source of accidental dynamic behavior.

---

## 70. Bounds Checking

Safe indexing of arrays, lists, bytes, and slices performs bounds checking.

Out-of-range indexing panics.

Checked APIs return an optional value.

```lua
local item = values:get(index)
```

Unsafe unchecked indexing requires an explicit unsafe operation.

The compiler may eliminate bounds checks when it can prove an access is safe.

---

## 71. Arrays

Fixed-size arrays have type:

```text
[T; N]
```

Example:

```lua
local bytes: [u8; 4] = [0, 1, 2, 3]
```

A bracket literal fills an array where the type calls for one, and it must have exactly `N` elements. This is the same contextual typing an integer literal takes (LR39): what the literal is written as does not change, only what it fills.

`N` is compile-time known.

Arrays are value types when their element type permits it.

Dynamic collections use `List<T>` or equivalent standard-library types.

---

## 72. Pointer Types

Unsafe native pointer types include:

```text
*const T
*mut T
```

Raw pointers:

- may be null;
- are not garbage-collected ownership references;
- may not be dereferenced outside `unsafe`;
- are primarily intended for FFI and low-level libraries.

A raw pointer to an existing value is taken with the address-of operators, which are valid only inside `unsafe` and only on a binding whose storage is addressable:

```text
&value        *const T
&mut value    *mut T
```

```lua
unsafe
    native_clock(&mut result)
end
```

Taking the address of a temporary, of a `const` binding through `&mut`, or of a value the compiler may keep in a register without spilling is a compile-time error. The compiler guarantees that an addressable binding stays put for the duration of the enclosing `unsafe` block, and makes no promise beyond it: storing a raw pointer past that point is the programmer's responsibility.

Managed references are never written as raw pointers in source, and there is no operator that converts one into the other outside `unsafe` reinterpretation.

---

## 73. ABI-Stable Layout

Ordinary struct layout is optimized by the compiler and is not ABI-stable unless explicitly annotated.

```lua
@repr("C")
struct Header
    kind: u32
    size: u64
end
```

Other explicit representations may be introduced:

```text
@repr("packed")
@repr("transparent")
```

Unsafe or foreign-layout annotations must document alignment and validity constraints.

---

## 74. Serialization

Serialization is not magical for every type.

A type may opt into generated serialization support through decorators.

```lua
@derive(Json)
struct User
    id: u64
    name: string
end
```

The exact derives belong to libraries.

LuaR provides sufficient compile-time metadata support for these libraries without requiring runtime reflection everywhere.

---

## 75. Derivation

A standardized decorator mechanism may derive common interfaces.

```lua
@derive(Eq, Hash, Display)
struct Point
    x: int
    y: int
end
```

Derivation expands into ordinary conforming implementations.

Generated implementations are visible to diagnostics and tooling.

`@derive` applies to a `struct` or an `enum`. Each name in it is a protocol (LR35), and the compiler derives these:

```text
Eq          function eq(self, other: Self): bool
Hash        function hash(self): u64
Display     function display(self): string
```

`Eq` compares every field, and for an enum the variant before its payload. `Hash` combines those same fields, so two values `eq` holds for hash alike. `Display` writes a struct the way its literal is written and an enum as the variant path, carrying the payload where there is one.

Deriving a protocol requires every field, and every payload of every variant, to have it already. A primitive has all three. Any other field type must have the member the protocol names, and one that does not is an error naming that field.

A derived member and a member of the same name written by hand collide. Deriving `Eq` for a type that already declares `eq` is an error, not an override, because either could be the one the author meant.

A name `@derive` does not recognize belongs to the package defining it (LR23.1). Until that package expands it, the type has members the compiler cannot enumerate, and reading one is not an error.

---

## 76. Method Resolution

Method resolution follows deterministic priority:

1. inherent methods declared on the type;
2. methods required by an explicitly selected interface context;
3. methods from extension blocks in scope (LR20).

Each step is fully resolved before the next is considered, so adding an inherent method to a type shadows an extension method of the same name. That is a source-compatible change for the type's author and a compile-time diagnostic, not a silent behavior change, at every call site relying on the extension.

Two extension blocks in scope defining the same method for the same type is a compile-time error at the call site. It is resolved by naming the block:

```lua
StringSlug.slug(title)
```

There is no runtime monkey-patching of method tables in statically typed code.

---

## 77. Dynamic Libraries

A compiled package may produce:

- an executable;
- a static library;
- a dynamic/shared library;
- a WebAssembly module;
- implementation-defined intermediate artifacts.

Exporting a foreign ABI symbol requires explicit annotation.

Ordinary language exports are language-level module exports, not automatically operating-system symbol exports.

---

## 78. Program Initialization

Module initialization occurs before `main` for modules reachable from the entry module.

Initialization order follows the dependency graph.

Within one module, top-level initializers execute in source order.

Programs should not depend on initialization order between unrelated modules.

A dependency cycle that makes initialization order observable before values are initialized is rejected.

---

## 79. Constant Values

`const` values initialized entirely from compile-time expressions may be embedded directly into generated code.

```lua
const maxConnections = 1024
```

Compile-time constants may include:

- booleans;
- integers;
- floats;
- strings;
- enum values;
- tuples;
- immutable records composed entirely of constants;
- compiler-supported type metadata.

Whether a constant occupies storage is not observable unless its address is explicitly requested through unsafe facilities.

---

## 80. Error Diagnostics as a Language Requirement

A conforming compiler should produce source-oriented diagnostics with:

- exact source ranges;
- expected and actual types;
- actionable notes for failed inference;
- import/module traces where relevant;
- decorator expansion context;
- generic instantiation context.

Diagnostic wording is not standardized, but source semantics should be designed so common failures can be explained without exposing compiler internals.

---

## 81. Reserved Syntax

These words are reserved and rejected rather than treated as identifiers, though LuaR assigns them no meaning:

```text
comptime    -- general compile-time execution; ruled out in LR24
effect      -- effect annotations
impl        -- alternative implementation-block syntax
macro       -- textual or syntactic macros; ruled out in LR24
yield       -- generators and coroutines
```

These syntactic spaces are reserved for the compiler and must not be given library-level meanings:

```text
@name       -- decorator syntax (LR23)
#if         -- conditional compilation (LR48)
#[...]      -- attribute syntax, should one ever be introduced
```

`unsafe` and `where` are not reserved-for-later; they are live keywords defined in LR29.2 and LR19.

---

## 82. Example Program

```lua
import { serve, Request, Response } from "std/http"
import { json } from "std/encoding"

@derive(Json)
struct User
    id: u64
    name: string
end

enum ApiError
    NotFound
    InvalidId
end

const users = [
    User { id = 1, name = "Alice" },
    User { id = 2, name = "Bob" },
]:frozen()

function findUser(id: u64): User?
    for user in users do
        if user.id == id then
            return user
        end
    end

    return nil
end

@route("/users/:id")
async function getUser(request: Request): Result<Response, ApiError>
    local raw = request.params:get("id"):okOr(ApiError.InvalidId)?

    local id = raw
        :parse<u64>()
        :mapErr((_) => ApiError.InvalidId)?

    local user = findUser(id):okOr(ApiError.NotFound)?

    return Result.Ok(Response.json(user))
end

export async function main(): Result<(), Error>
    await serve({
        address = "0.0.0.0:8080",
        routes = [getUser],
    })?

    return Result.Ok(())
end
```

The example demonstrates the intended feel of LuaR:

- Luau-like declarations and blocks;
- native typed values;
- nominal structs;
- enums;
- optionals;
- `Result`;
- error propagation;
- decorators;
- async functions;
- typed modules;
- ordinary application I/O.

---

## 83. Example CLI

```lua
import process from "std/process"
import fs from "std/fs"

enum Command
    Print(string)
    Count(string)
end

function parseArgs(args: List<string>): Result<Command, string>
    match args
        case [_, "print", path]
            return Result.Ok(Command.Print(path))

        case [_, "count", path]
            return Result.Ok(Command.Count(path))

        case _
            return Result.Err("usage: app <print|count> <path>")
    end
end

-- Sequence patterns (LR16.2) match a list by shape. The wildcard skips argv[0],
-- and `case _` is required because a list is not a closed type.

export function main(args: List<string>): int
    local command = parseArgs(args)

    match command
        case Result.Err(message)
            process.stderr:writeLine(message)
            return 1

        case Result.Ok(Command.Print(path))
            local text = fs.readText(path)

            match text
                case Result.Ok(value)
                    print(value)
                    return 0

                case Result.Err(error)
                    process.stderr:writeLine(error:display())
                    return 1
            end

        case Result.Ok(Command.Count(path))
            local text = fs.readText(path)

            match text
                case Result.Ok(value)
                    print(value.byteLength)
                    return 0

                case Result.Err(error)
                    process.stderr:writeLine(error:display())
                    return 1
            end
    end
end
```

---

## 84. Example Generic Collection API

```lua
interface Iterator<T>
    function next(self): T?
end

interface Iterable<T>
    function iterator(self): Iterator<T>
end

function collect<T>(source: Iterable<T>): List<T>
    local result = List<T>.new()

    for value in source do
        result:push(value)
    end

    return result
end
```

The compiler may specialize generic code, but source semantics remain independent of specialization strategy.

---

## 85. Example Native Interop

```lua
@repr("C")
struct CTime
    seconds: i64
    nanos: i32
end

@extern("c")
unsafe function native_clock(out: *mut CTime): i32

function currentNativeTime(): Result<CTime, Error>
    local value = CTime {
        seconds = 0,
        nanos = 0,
    }

    unsafe
        -- `value` is an addressable local, so &mut is valid for the
        -- duration of this block (LR72).
        if native_clock(&mut value) ~= 0 then
            return Result.Err(Error("native_clock failed"))
        end
    end

    return Result.Ok(value)
end
```

Safe application code should normally consume a wrapper rather than invoking foreign APIs directly.

---

## 86. Example Decorator

A conceptual decorator declaration may look like:

```lua
decorator Serializable(target: TypeDeclaration)
    if target.kind ~= "struct" then
        target:report("@Serializable can only be applied to structs")
        return
    end

    target:addImplementation("Serialize", generateSerializer(target))
end
```

The exact decorator-definition API remains a language/tooling surface separate from ordinary runtime APIs.

What matters semantically is that decorator expansion is compile-time, typed, deterministic, inspectable, and incapable of arbitrary hidden runtime mutation.

---

## 87. Design Boundaries

LuaR is deliberately not defined as:

- Lua with a native backend;
- Luau with extra standard-library functions;
- a Luau-compatible runtime;
- a dynamically typed language with optional annotations;
- a Rust-like ownership language with Lua syntax;
- a class-inheritance language;
- a macro-heavy language where ordinary semantics are library tricks.

LuaR is a distinct compiled language with Luau ancestry.

Compatibility with Lua or Luau source code is not a LuaR goal. Familiar source may work with small changes where the semantics align, but new language features and corrected semantics take precedence over compatibility.

---

## 88. Core Semantic Summary

A concise description of LuaR is:

```text
Syntax:
    Luau-derived, block-based, lightweight, readable.

Execution:
    Compiled only.

Typing:
    Static, inferred, structural for records, nominal for structs,
    enums, and interfaces.

Numbers:
    Real integer and floating-point types. int is i64 everywhere.
    / is float division, // is integer division, overflow always traps.

Booleans:
    No truthiness. Conditions and and/or/not are bool only.

Data:
    Structs (value), ref structs (reference), records, tuples,
    lists, maps, arrays, enums.

Literals:
    [...] is always a sequence, { ... } is always a record,
    Map { ... } is always a map. = binds values, : introduces types.

Nullability:
    Explicit through T?, with ?. and ?? and narrowing.

Errors:
    Result plus ? for expected failure, unchecked exceptions for
    exceptional failure, panic for violated invariants.

Memory:
    Automatic management with deterministic cleanup for external resources.
    Identity observable only for declared reference types.

Abstraction:
    Functions, generics, interfaces, composition, named extension blocks.

Metaprogramming:
    Compile-time decorators bounded to their target, opt-in reflection,
    no user-facing comptime, no macros, no metatable object model.

Modules:
    Static imports and exports with package-aware resolution.
    Mutable state is never exported.

Concurrency:
    async/await, structured tasks, native threads where needed.

Interop:
    Explicit unsafe native FFI and stable-layout annotations.

Indexing:
    Zero-based, bounds-checked, one loop form over explicit ranges.

Strings:
    UTF-8, no integer indexing, no slicing, explicit byte/char/grapheme APIs.

Global state:
    Explicit module-private declarations only.
```

---

## 89. Grammar Sketch

This is an illustrative grammar, not a normative parser grammar. It reflects the decisions recorded in LR90.

```ebnf
module          = { import_decl | declaration | statement } ;

declaration     = function_decl
                | extern_decl
                | struct_decl
                | enum_decl
                | interface_decl
                | extend_decl
                | type_decl
                | const_decl
                | decorated_decl ;

decorated_decl  = { decorator } declaration ;

decorator       = "@" identifier [ "(" argument_list ")" ] ;

function_decl   = [ "export" ]
                  [ "async" ]
                  [ "unsafe" ]
                  [ "static" ]
                  "function"
                  qualified_name
                  [ type_params ]
                  "(" [ parameter_list ] ")"
                  [ ":" type ]
                  [ where_clause ]
                  block
                  "end" ;

type_params     = "<" identifier { "," identifier } ">" ;

where_clause    = "where" constraint { "," constraint } ;

constraint      = identifier ":" type ;         (* "&" composes bounds (LR19) *)

extern_decl     = decorator                     (* @extern("abi") *)
                  "unsafe" "function"
                  identifier
                  "(" [ parameter_list ] ")"
                  [ ":" type ] ;                (* no body, no "end" *)

struct_decl     = [ "export" ]
                  [ "const" | "ref" ]
                  "struct"
                  identifier
                  [ type_params ]
                  [ "implements" type_list ]
                  { struct_member }
                  "end" ;

struct_member   = [ visibility ] ( field_decl
                                | function_decl
                                | property_decl ) ;

visibility      = "private" | "internal" | "public" ;

field_decl      = identifier ":" type [ "=" expression ] ;

property_decl   = "property" identifier ":" type
                  "get" block "end"
                  [ "set" "(" identifier ")" block "end" ]
                  "end" ;

enum_decl       = [ "export" ]
                  "enum"
                  identifier
                  [ type_params ]
                  { enum_variant }
                  "end" ;

enum_variant    = identifier [ "(" type_list ")" | record_type ] ;

interface_decl  = [ "export" ]
                  [ "structural" ]
                  "interface"
                  identifier
                  [ type_params ]
                  { interface_member }
                  "end" ;

interface_member
                = [ "async" ] "function" identifier [ type_params ]
                  "(" [ parameter_list ] ")" [ ":" type ]
                                                (* required, and has no body *)
                | identifier ":" type ;         (* a required property (LR18) *)

extend_decl     = [ "export" ]
                  "extend" identifier "for" type
                  { function_decl }
                  "end" ;

type_decl       = [ "export" ]
                  "type"
                  identifier
                  [ type_params ]
                  "="
                  type ;

statement       = local_decl
                | assignment
                | if_stmt
                | while_stmt
                | repeat_stmt
                | for_stmt
                | match_stmt
                | try_stmt
                | unsafe_block
                | defer_stmt
                | return_stmt
                | break_stmt
                | continue_stmt
                | throw_stmt
                | expression_stmt ;

local_decl      = "local" binding
                  [ ":" type ]
                  [ "=" expression ] ;

const_decl      = [ "export" ] "const" binding
                  [ ":" type ]
                  "=" expression ;

binding         = identifier
                | record_pattern             (* irrefutable only *)
                | tuple_pattern ;            (* irrefutable only *)

assignment      = lvalue assign_op expression ;

lvalue          = identifier
                | postfix_expr "." identifier
                | postfix_expr "[" expression "]" ;

expression_stmt = expression ;       (* whose outermost operation is a call *)

conditional     = "#if" expression { item }
                  { "#elseif" expression { item } }
                  [ "#else" { item } ]
                  "#end" ;                      (* LR48 *)
                  (* `item` is whatever the surrounding position holds: a
                     declaration at module level, a statement in a block *)

assign_op       = "=" | "+=" | "-=" | "*=" | "/=" | "//=" | "%="
                | "**=" | "&=" | "|=" | "^=" | "<<=" | ">>=" ;

if_stmt         = "if" expression "then" block
                  { "elseif" expression "then" block }
                  [ "else" block ]
                  "end" ;

while_stmt      = "while" expression "do" block "end" ;

repeat_stmt     = "repeat" block "until" expression ;

for_stmt        = "for" binding_list "in" expression "do" block "end" ;

match_stmt      = "match" expression
                  match_case { match_case }
                  "end" ;

match_case      = "case" pattern
                  [ "if" expression ]
                  ( "=>" expression | block ) ;
                  (* one arm form throughout a given match *)

unsafe_block    = "unsafe" block "end" ;

defer_stmt      = "defer" expression_stmt ;    (* a call, as LR89.1 requires *)

try_stmt        = "try" block
                  { catch_clause }
                  [ "finally" block ]
                  "end" ;

pattern         = or_pattern ;

or_pattern      = primary_pattern { "|" primary_pattern } ;

primary_pattern = typed_pattern ;

typed_pattern   = base_pattern [ "is" type ] ;   (* LR16.2 type pattern *)

base_pattern    = "_"
                | identifier
                | literal
                | range_pattern
                | path [ "(" pattern_list ")" | record_pattern ]
                | sequence_pattern
                | tuple_pattern
                | "(" pattern ")" ;

record_pattern  = "{" [ field_pattern { "," field_pattern } [ "," "..." ] ] "}" ;

field_pattern   = identifier [ "as" identifier ] [ "=" pattern ] ;

sequence_pattern
                = "[" [ elem_pattern { "," elem_pattern } ] "]" ;

elem_pattern    = pattern
                | "..." [ identifier ] ;     (* at most one per sequence *)

tuple_pattern   = "(" pattern "," [ pattern { "," pattern } ] ")" ;

range_pattern   = literal ( "..<" | "..=" ) literal ;

type            = union_type ;

union_type      = intersection_type { "|" intersection_type } ;

intersection_type
                = postfix_type { "&" postfix_type } ;

postfix_type    = primary_type { "?" } ;

primary_type    = identifier [ type_args ]
                | function_type
                | tuple_type
                | record_type
                | array_type
                | pointer_type
                | "(" type ")" ;

function_type   = [ "async" ] "(" [ type_list ] ")" "->" type ;

tuple_type      = "(" ")" | "(" type "," [ type_list ] ")" ;

array_type      = "[" type ";" const_expression "]" ;

pointer_type    = ( "*const" | "*mut" ) type ;

expression      = literal | identifier | unary_expr | binary_expr
                | postfix_expr | range_expr | primary_expr ;
                  (* LR11.7 states precedence and associativity *)

range_expr      = [ expression ] ( "..<" | "..=" ) [ expression ] ;

primary_expr    = literal
                | identifier
                | tuple_literal
                | list_literal
                | record_literal
                | map_literal
                | function_expr
                | match_expr
                | if_expr
                | address_of_expr            (* unsafe contexts only *)
                | "(" expression ")" ;

list_literal    = "[" [ expression_list ] "]" ;

record_literal  = [ path ] "{" [ field_init { "," field_init } [ "," ] ] "}" ;

map_literal     = "Map" "{" [ map_entry { "," map_entry } [ "," ] ] "}" ;

field_init      = identifier "=" expression ;

map_entry       = identifier "=" expression
                | "[" expression "]" "=" expression ;

tuple_literal   = "(" ")" | "(" expression "," [ expression_list ] ")" ;

address_of_expr = ( "&" | "&mut" ) lvalue ;
```

### 89.1 Settled Syntax Interactions

The interactions that previously blocked a normative grammar are decided.

**Type arguments versus comparison.** In expression position, `name <` begins a type-argument list only when the tokens through the matching `>` parse as a type list *and* the token after `>` is `(`. Type arguments in expression position only ever precede a call, so `json.decode<User>(text)` is a generic call. No turbofish is required and the rule needs only bounded lookahead.

The rule cannot take a comparison away from a program that has one. `a < b > (c)` matches it and reads as a call, and its reading as a comparison was never valid: comparison does not chain (LR11.7). Anything that does compare a comparison is parenthesized, `(a < b) == c`, and parentheses keep it out of the rule's way.

**Ranges versus concatenation and float literals.** `..`, `..<`, and `..=` are three distinct tokens (LR10.4). Bare `..` is always concatenation and no range is spelled with it. `0..<10` cannot lex as a float because `0.` requires a following digit.

**Tuple types versus function types.** A parenthesized type list is a tuple unless `->` follows it (LR14).

**Expression statements.** A statement that is an expression must be one whose outermost operation is a call: `f(x)`, `x:method()`, `await f(x)`, and either of those with `?`. Anything else computes a value and discards it, which is a mistake rather than a program, and the most common one is a compound assignment that does not exist: `text ..= suffix` is a range (LR10.4) evaluated for nothing, not a concatenation (LR5.4).

**Match arm extent.** A `match` uses block arms or `=>` arms throughout, never both (LR16.1), so a block arm ends unambiguously at the next `case` or at `end`.

**Value binding versus type annotation.** `=` binds a value in record literals, map literals, struct literals, named arguments, and field defaults. `:` introduces a type and nothing else. Renaming, in both imports and destructuring, uses `as`.

**`is`.** `is` always takes a type on its right. Identity is `std/mem.identical` (LR32).

**Method calls versus member access.** `:` calls a method, `.` reaches fields, properties, tuple elements, static functions, enum variants, and module members (LR12.2). Neither spelling is a fallback for the other.

**Foreign declarations.** `extern_decl` is its own production with no body, so a bodiless signature is not a malformed `function_decl`.

**Unsafe blocks versus the `unsafe` modifier.** A function declaration is not a statement, so it cannot open a block. `unsafe` followed by `function` or `static` is therefore always the modifier on a declaration (LR46), and `unsafe` followed by anything else opens a block that runs to its `end` (LR29.2).

---

## 90. Settled Design Decisions

An earlier draft left twenty questions open. Each is decided below, with the section that specifies it and the reasoning. They are recorded rather than deleted so a future revision can see what was traded away.

**1. Collection mutability naming.** `List<T>`, `Map<K, V>`, and `Set<T>` are mutable; the immutable forms are `FrozenList<T>`, `FrozenMap<K, V>`, and `FrozenSet<T>` (LR59). Most code builds and returns mutable collections, and a scheme that gives the common case the longer name gets routed around rather than followed. Frozen types have no mutating methods, so immutability is checked rather than trapped.

**2. The role of exceptions.** Exceptions are unchecked and absent from signatures. `Result` is the standard for expected failure and every fallible standard-library API returns it (LR25.3). Checked exceptions push transitive failure sets into every signature; silent but common exceptions defeat `Result` entirely. Exceptions are left to foreign boundaries and cross-cutting aborts.

**3. Width of `int`.** `int` is exactly `i64` and `uint` exactly `u64` on every target (LR4.3). Native-width integers make overflow, serialization, and hashing depend on the host, which contradicts predictable compiled semantics. `isize` and `usize` exist separately for FFI and allocator code.

**4. Record and map literal syntax.** `[...]` is always a sequence, `{ ... }` always a structural record, `Map { ... }` always a map (LR13.2). Context never changes what kind of thing a literal constructs, so no literal is a record in one place and a map in another. Which sequence a `[...]` fills does come from context, the way the type of an integer literal does (LR39, LR71). The cost is six characters where a dynamic map is created; the gain is that reading a literal tells you its shape without reading its destination.

**5. Extension method scoping.** Extension blocks are named, exported, and imported like any other declaration, and are in scope only where declared or imported (LR20). Ambient extensions mean importing a module for one function can silently change what an unrelated method call resolves to.

**6. Reflection opt-in.** `@reflect` (LR34). Reflection is metadata rather than behavior: an interface would imply members the type does not have and would let reflectability be demanded by a signature, and a dedicated modifier would duplicate what decorators already express.

**7. What decorators may generate.** A decorator may add members and interface implementations to the declaration it is attached to, and may not introduce new top-level declarations (LR23.1). This keeps every name in a module traceable to something written in it, which grep, go-to-definition, and human readers all rely on.

**8. `is` and identity.** `is` is a type test only; identity is `identical(a, b)` from `std/mem`, defined only on types with observable identity (LR32). Overloading one operator on whether the name to its right is a type or a binding makes a line's meaning depend on name resolution, and breaks under shadowing.

**9. Properties in the core.** Kept, with constraints: cheap, idempotent, non-failing, non-async (LR43). Without them, promoting a stored field to a computed value is a breaking API change, so authors pre-emptively wrap every field in accessors and callers read `getName()` forever.

**10. Compile-time execution.** No user-facing `comptime`. Compile-time evaluation lives in `const` initializers and the decorator API, and nowhere else (LR24). A general compile-time sublanguage is a second language inside the first, with its own scoping rules, failure modes, and consequences for build reproducibility.

**11. Multiple return values.** Removed. A function returns exactly one value; returning several means returning a tuple, and `local (a, b) = f()` is destructuring sugar (LR9.7). Lua's adjusting multiple-value convention has no static typing story and truncates depending on argument position.

**12. Range syntax.** `a..<b` exclusive and `a..=b` inclusive, with no bare `..` range (LR10.4). `..` stays concatenation, which is the operator Lua programmers reach for daily. The consequence is that `..=` is unavailable as compound concat-assign, so `text = text .. suffix` is written out (LR5.4).

**13. Integer division.** `//` is integer division; `/` is float division and is a compile-time error on two integers (LR11.1). Silently truncating `10 / 3` to `3` is exactly the lossy implicit behavior LR4.4 already rules out for conversions.

**14. `and` and `or`.** Bool operands, bool result (LR11.4). Value-returning `and`/`or` depends on truthiness, which LuaR does not have, and silently discards legitimate `0` and `""` values. `??` and `if` expressions cover the idioms it replaces.

**15. Overflow checking across modes.** Integer overflow traps in every compilation mode, release included (LR4.3). Mode-dependent arithmetic means the program that was tested is not the program that ships. Wrapping, saturating, and checked operations are explicit methods.

**16. Interface conformance.** Nominal by default, `structural interface` as opt-in (LR18). Conformance is a claim about behavior, and accidental structural matches turn unrelated renames into breaking changes. Structural remains available for narrow protocols and for adapting foreign types.

**17. Observable object identity.** Only for types that declare reference semantics: `ref struct`, closures, interface values, and reference-backed collections (LR32). Universal identity would forbid copying, inlining, unboxing, and interning value types.

**18. Optional versus `Result` propagation.** `?` propagates `Result` only; there is no optional propagation operator (LR25.2). One operator with two meanings would require knowing the enclosing signature to read a call site, and would be genuinely ambiguous on `Result<T?, E>`. Optionals convert with `:okOr(error)`.

**19. Exported mutable state.** Forbidden. `export` applies to functions, types, interfaces, extension blocks, and `const` values (LR52). Exported mutable state makes every module a hidden input to every other, and cannot be synchronized by a caller who sees only the name.

**20. A reference-semantics nominal type.** Added as `ref struct` (LR31), a modifier on the existing construct rather than a new declaration form. Shared, identifiable, mutable objects are a real need that value structs silently mismodel by copying. It grants reference semantics, identity, and finalizers, and deliberately does not grant inheritance.

---

## 91. Final Character

Code in LuaR should feel immediately approachable to someone coming from Luau:

```lua
function greet(user: User)
    if user.name ~= "" then
        print(`Hello, {user.name}`)
    end
end
```

But it should also support programs that Luau was never designed around:

```lua
@derive(Json, Eq)
export struct User
    id: UserId
    name: string
    email: string?
end

export interface Repository<T>
    async function find(self, id: u64): Result<T?, DbError>
    async function save(self, value: T): Result<(), DbError>
end

export async function loadUser(
    repository: Repository<User>,
    id: u64,
): Result<User, Error>
    local found = await repository:find(id)?          -- User?
    local user = found:okOr(Error(`user {id} was not found`))?
    return Result.Ok(user)
end
```

LuaR retains Luau's low-friction surface while giving compiled general-purpose software its own native vocabulary instead of forcing everything through Lua's historical table, number, metatable, and runtime-module model.
