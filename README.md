<div align="center">
  <img src="./assets/luaRWordmark.png" width="300" />

  <p>
    A compiled evolution of Lua, inspired by Luau and designed for general-purpose programming.
  </p>
</div>

## Status

LuaR is in development. There are no releases yet.

Everything below is what LuaR is meant to be, not what you can run today.

## A first look

```lua
import { readText } from "std/fs"
import { json } from "std/encoding"

struct Config
    host: string
    port: u16
end

export function main(): Result<(), Error>
    local text = readText("./config.json")?
    local config = json.decode<Config>(text)?

    print(`serving on {config.host}:{config.port}`)
    return Result.Ok(())
end
```

Blocks end with `end`, functions are values, strings interpolate with backticks. What Luau does not have: `u16` is a 16-bit integer, `Config` has a fixed layout, and `?` returns from `main` if reading or decoding fails.

## Structs, interfaces, and generics

Structs are nominal and have a fixed layout. Methods take `self` explicitly, and `:` calls them.

```lua
interface Display
    function display(self): string
end

struct Vec2 implements Display
    x: float
    y: float

    static function zero(): Vec2
        return Vec2 { x = 0.0, y = 0.0 }
    end

    function length(self): float
        return math.sqrt(self.x ** 2 + self.y ** 2)
    end

    function display(self): string
        return `({self.x}, {self.y})`
    end
end
```

Implementing an interface requires saying `implements`. A struct that happens to have a matching `display` method does not satisfy `Display` by accident, so renaming an unrelated method never silently breaks a caller. Interfaces whose contract really is just their shape opt out with `structural`.

```lua
structural interface Readable
    function read(self): bytes
end
```

Generic constraints go in a `where` clause, after the signature and before the body.

```lua
function max<T>(a: T, b: T): T
where T: Comparable
    return if a > b then a else b
end
```

## Enums and pattern matching

Enums carry data, and `match` has to cover every case or the program does not compile.

```lua
enum Shape
    Circle(float)
    Rect { width: float, height: float }
end

function area(shape: Shape): float
    return match shape
        case Shape.Circle(radius) => math.pi * radius * radius
        case Shape.Rect { width, height } => width * height
    end
end
```

Patterns destructure records, structs, tuples, and lists, and they take guards.

```lua
match request
    case Request.Get(path) if path.startsWith("/api")
        return handleApi(path)

    case Request.Get(path)
        return serveFile(path)

    case Request.Post(path, body)
        return handlePost(path, body)
end
```

## Errors are values

Functions that can fail return `Result`, and `?` propagates the failure to the caller.

```lua
function loadUser(path: string): Result<User, Error>
    local text = fs.readText(path)?
    local user = json.decode<User>(text)?
    return Result.Ok(user)
end
```

Absence is separate from failure. `T?` marks a value that may be missing, `?.` chains through it, and `??` supplies a default.

```lua
local city = user?.address?.city ?? "unknown"
```

Exceptions exist for foreign boundaries and cross-cutting aborts. No standard library function throws one for an expected failure.

## Cleanup with defer

`defer` runs an expression when the scope exits, so cleanup sits next to the thing it cleans up.

```lua
function copyFile(from: string, to: string): Result<(), IoError>
    local source = File.open(from)?
    defer source:close()

    local target = File.create(to)?
    defer target:close()

    return target:writeAll(source:readAll()?)
end
```

Deferred expressions run in reverse order of registration, on every exit from the scope. That includes the two `?` operators above returning early, which is the case a manual `close()` at the bottom of the function gets wrong.

## Async

Async functions return a task. Structured scopes make sure the tasks they start finish or get cancelled before the scope exits.

```lua
async function loadUser(id: u64): Result<User, Error>
    local response = (await http.get(`/users/{id}`))?
    return json.decode<User>(response.body)
end

async function loadBoth(): Result<(User, User), Error>
    async scope tasks
        local first = tasks.spawn(loadUser(1))
        local second = tasks.spawn(loadUser(2))

        return Result.Ok(((await first)?, (await second)?))
    end
end
```

## Decorators

Decorators run in the compiler, not at runtime. They generate implementations, register routes, and mark tests.

```lua
@derive(Json, Eq)
export struct User
    id: u64
    name: string
    email: string?
end

@route("/users/:id")
async function getUser(request: Request): Result<Response, ApiError>
    ...
end

@test
function unitCircle()
    assert(area(Shape.Circle(1.0)) == math.pi)
end
```

A decorator can only touch the declaration it is attached to. `@derive(Json)` on `User` can add a `Serialize` implementation for `User`, and it cannot declare a `UserBuilder` next to it. Every name in a file therefore comes from something written in that file, which is what keeps grep and go-to-definition honest.

## Extension methods

Extension blocks add methods to a type you did not declare, resolved at compile time. They are named, exported, and imported like anything else.

```lua
-- text/slug.luar
export extend StringSlug for string
    function slug(self): string
        return self:lower():replace(" ", "-")
    end
end
```

```lua
import { StringSlug } from "text/slug"

local path = title:slug()
```

Most languages with extension methods make them ambient, so importing a module for one function can quietly change what an unrelated method call resolves to elsewhere in the file. Naming the block means `title:slug()` only works where you asked for it, and an unknown-method error can tell you which block to import.

## What changed from Lua

**Numbers are typed.** `i8` through `i64`, `u8` through `u64`, `f32`, `f64`. `int` is exactly 64 bits on every target. Overflow traps instead of wrapping, in release builds too.

**Division split in two.** `//` divides integers, `/` divides floats. Writing `10 / 3` on two integers is a compile error rather than a silent `3`.

**Indexing starts at zero.** Lists, arrays, bytes, and slices all start at 0. There is one loop form, over an explicit range: `for i in 0..<values.length`.

**There is no truthiness.** Conditions must be `bool`. `if user then` does not compile when `user` is `User?`; write `if user ~= nil then`. `and` and `or` take booleans and return booleans, so `x or default` becomes `x ?? default`.

**Tables split into four types.** `[...]` is a list, `{ ... }` is a record with statically known fields, `Map { ... }` is a dynamic map, and `struct` declares a nominal type with a fixed layout. Which one a literal builds never depends on context.

**No metatables.** Methods, interfaces, operator protocols, decorators, and extension methods replace them. Object behavior is declared, not patched at runtime.

**Strings are UTF-8 and are not arrays.** No integer indexing, no slicing. Iterate bytes, Unicode scalars, or graphemes. There is no `text.length`, because those three counts differ.

**Modules instead of a global table.** Every file is a module. Declarations are private until exported, imports resolve at compile time, and implicit globals are an error.

## Non-goals

LuaR does not aim to run Lua or Luau code. Familiar source may work with small changes where the semantics line up, but correcting Lua's defaults takes priority over compatibility.

It is also not a dynamically typed language with optional annotations, not an ownership language with Lua syntax, and not built around class inheritance.

## License

luaR is MIT licensed. See [LICENCE](LICENCE) for details.
