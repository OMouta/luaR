# LuaR standard library specification

> Working specification for the standard library shipped with LuaR.

<!-- normative: STD1-STD21 -->

## 1. Contract

Sections STD1 through STD21 are normative. The `normative` directive at the top of this file is the machine-readable source for standard-library conformance coverage.

The language specification defines syntax, types, evaluation, and the boundary between the compiler and standard modules. This specification defines the library available through that boundary.

Every module named here ships with the compiler. Importing one does not require a package dependency.

An operation that can fail during ordinary use returns `Result`. It does not throw. Invalid arguments that violate a stated precondition trap. Allocation failure may abort the process.

`Error` is the common error type unless a section defines a more useful error enum. An `Error` identifies the operation and the affected resource. Its message is not a stable interface.

Strings contain UTF-8. `bytes` contains uninterpreted bytes. An API does not use the process locale unless its section says so.

Paths are strings in the platform's native path syntax. Path operations do not require valid UTF-8 beyond LuaR's string representation.

Lengths and offsets use `int` unless they cross a native ABI boundary. A count cannot be negative. A range with an exclusive upper bound follows LR10.4.

An API that accepts a `FrozenList`, `FrozenMap`, or `FrozenSet` does not mutate it. An API that returns a frozen collection may share its storage with the library.

Platform-dependent behavior is stated explicitly. An unsupported operation returns `Err`; it does not silently do something weaker.

## 2. `std/prelude`

`std/prelude` is in scope as defined by LR54.1. It exports the standard protocols from LR35:

```lua
Eq
Hash
Display
Comparable
Iterator<T>
Iterable<T>
Index<K, V>
Into<T>
```

It provides these methods:

```lua
List<T>.contains(value: T): bool where T: Eq
List<T>.indexOf(value: T): int? where T: Eq
List<T>.insert(index: int, value: T): ()
List<T>.removeAt(index: int): T
List<T>.reverse(): ()
List<T>.pushAll(other: List<T>): ()
List<T>.pushAll(other: FrozenList<T>): ()
List<T>.enumerated(): Iterable<(int, T)>

FrozenList<T>.contains(value: T): bool where T: Eq
FrozenList<T>.indexOf(value: T): int? where T: Eq
FrozenList<T>.enumerated(): Iterable<(int, T)>

T?.okOr<E>(error: E): Result<T, E>
Result<T, E>.mapErr<F>(map: (E) -> F): Result<T, F>
```

List mutation and search behave as specified by LR13.1. `enumerated` yields each zero-based index and value in list order. `okOr` returns `Ok` for a present value and `Err(error)` for `nil`. `mapErr` leaves `Ok` unchanged and applies `map` once to `Err`.

## 3. `std/collections`

`std/collections` exports algorithms written against the protocols from `std/prelude`:

```lua
collect<T>(source: Iterable<T>): List<T>
map<T, U>(source: Iterable<T>, transform: (T) -> U): List<U>
filter<T>(source: Iterable<T>, keep: (T) -> bool): List<T>
fold<T, A>(source: Iterable<T>, initial: A, combine: (A, T) -> A): A
any<T>(source: Iterable<T>, predicate: (T) -> bool): bool
all<T>(source: Iterable<T>, predicate: (T) -> bool): bool
count<T>(source: Iterable<T>): int

sort<T>(values: List<T>): () where T: Comparable
sortBy<T>(values: List<T>, compare: (T, T) -> int): ()
```

Algorithms consume one iterator. They preserve iteration order unless the operation is `sort` or `sortBy`.

`map` and `filter` call their function once per visited value. `fold` applies `combine` from first to last. `any` stops at the first `true`; `all` stops at the first `false`.

`sort` and `sortBy` are stable. A comparison result below zero orders the left value first, zero preserves input order, and a result above zero orders the right value first.

The module also exports a double-ended queue:

```lua
Deque.new<T>(): Deque<T>
Deque<T>.pushFront(value: T): ()
Deque<T>.pushBack(value: T): ()
Deque<T>.popFront(): T?
Deque<T>.popBack(): T?
Deque<T>.front(): T?
Deque<T>.back(): T?
Deque<T>.clear(): ()
Deque<T>.length: int
```

## 4. `std/mem`

`std/mem` exports the operations that require an explicit memory boundary:

```lua
identical<A, B>(left: A, right: B): bool
sizeOf<T>(): usize
alignOf<T>(): usize

unsafe bytesOf(text: string): *const u8
unsafe stringFromBytes(data: *const u8, length: int): string
unsafe reinterpret<T, U>(value: T): U
```

`identical` follows LR32. `sizeOf` and `alignOf` report the target ABI layout used by foreign calls. They are compile-time constants after monomorphization.

`bytesOf` returns the address of the first UTF-8 byte of `text`. The address remains valid while `text` is reachable. It is not zero-terminated.

`stringFromBytes` copies `length` bytes. The caller guarantees that `length` is nonnegative, the range is readable, and the bytes are valid UTF-8.

`reinterpret` follows LR72. `T` and `U` must have the same size and ABI-representable layouts. It copies the value's representation without conversion.

## 5. `std/fs`

`std/fs` exports whole-file operations:

```lua
readText(path: string): Result<string, Error>
writeText(path: string, text: string): Result<(), Error>
appendText(path: string, text: string): Result<(), Error>

readBytes(path: string): Result<bytes, Error>
writeBytes(path: string, data: bytes): Result<(), Error>
appendBytes(path: string, data: bytes): Result<(), Error>

exists(path: string): Result<bool, Error>
metadata(path: string): Result<Metadata, Error>
readDir(path: string): Result<List<DirEntry>, Error>
createDir(path: string): Result<(), Error>
createDirAll(path: string): Result<(), Error>
removeFile(path: string): Result<(), Error>
removeDir(path: string): Result<(), Error>
removeDirAll(path: string): Result<(), Error>
copy(from: string, to: string): Result<(), Error>
rename(from: string, to: string): Result<(), Error>
```

```lua
export enum FileType
    File
    Directory
    Symlink
    Other
end

export struct Metadata
    kind: FileType
    length: u64
    readonly: bool
end

export struct DirEntry
    name: string
    path: string
    kind: FileType
end
```

`readText` reads the whole file and validates UTF-8. Invalid UTF-8 is `Err`.

`writeText` replaces the file with the UTF-8 bytes of `text`. `appendText` creates the file where it is absent and otherwise appends without changing existing bytes.

The byte variants perform the same operations without encoding or validation.

`exists` returns `Ok(false)` only when the path does not exist. Permission and I/O failures are `Err`.

`readDir` returns direct children only. It does not promise an order. Each entry's `name` is relative to the directory and `path` is the joined path passed to metadata operations.

`createDir` creates one directory. `createDirAll` also creates missing parents and succeeds when the directory already exists.

`removeDir` requires an empty directory. `removeDirAll` removes the directory tree and returns `Err` when `path` names a symlink rather than following it.

`copy` copies one regular file and replaces an existing destination file. `rename` uses the platform's atomic rename where available. Cross-filesystem moves return `Err`.

## 6. `std/io`

`std/io` exports process stream operations:

```lua
readLine(): Result<string?, Error>
readAll(): Result<bytes, Error>

write(text: string): Result<(), Error>
writeLine(text: string): Result<(), Error>
writeBytes(data: bytes): Result<(), Error>
flush(): Result<(), Error>

writeError(text: string): Result<(), Error>
writeErrorLine(text: string): Result<(), Error>
flushError(): Result<(), Error>
```

Input functions read standard input. Output functions without `Error` in their name write standard output; the others write standard error.

`readLine` removes one trailing line ending. It accepts `\n` and `\r\n`. It returns `Ok(nil)` at end of input before another byte is read. Invalid UTF-8 is `Err`.

`readAll` returns the remaining bytes without decoding them.

`writeLine` and `writeErrorLine` append `\n`, independent of the platform's native text convention. No write function flushes implicitly.

## 7. `std/path`

`std/path` performs lexical path operations:

```lua
separator: string

join(left: string, right: string): string
normalize(path: string): string
parent(path: string): string?
fileName(path: string): string?
stem(path: string): string?
extension(path: string): string?
isAbsolute(path: string): bool
isRelative(path: string): bool
```

These functions do not access the filesystem. They use the target platform's path rules.

If `right` is absolute, `join(left, right)` returns `normalize(right)`. Otherwise it inserts one separator and normalizes the result.

`normalize` removes redundant separators and `.` components. It resolves `..` only where a preceding ordinary component exists. It preserves a leading root and does not resolve symlinks.

`fileName` returns the final ordinary component. `stem` removes the final extension from that name. `extension` excludes the leading dot and returns `nil` where the name has no extension. A leading dot by itself does not start an extension.

## 8. `std/process`

`std/process` exports information about the current process and a blocking child-process API:

```lua
args(): FrozenList<string>
id(): u64
currentDirectory(): Result<string, Error>
setCurrentDirectory(path: string): Result<(), Error>
exit(code: int): never

Command.new(program: string): Command
Command.arg(value: string): Command
Command.args(values: FrozenList<string>): Command
Command.currentDirectory(path: string): Command
Command.environment(name: string, value: string): Command
Command.removeEnvironment(name: string): Command
Command.clearEnvironment(): Command
Command.status(): Result<ExitStatus, Error>
Command.output(): Result<Output, Error>
```

```lua
export struct ExitStatus
    code: int?
    success: bool
end

export struct Output
    status: ExitStatus
    stdout: bytes
    stderr: bytes
end
```

`args` includes the executable path at index zero. The returned list does not change.

`exit` terminates without running remaining deferred expressions or finalizers. Returning from `main` is preferred where cleanup matters.

Each `Command` builder method returns the same command after mutation. Arguments pass directly to the child without shell parsing. `status` inherits the parent's streams. `output` captures standard output and standard error. Neither operation treats a nonzero exit code as `Err`.

## 9. `std/env`

`std/env` exports environment-variable operations:

```lua
get(name: string): string?
set(name: string, value: string): Result<(), Error>
remove(name: string): Result<(), Error>
variables(): Result<FrozenMap<string, string>, Error>
```

`get` returns `nil` where the variable is not set. An empty value is a present empty string.

Names and values cannot contain a zero byte. `set` and `remove` return `Err` for an invalid name or a platform failure.

`variables` returns a snapshot. On platforms with case-insensitive names, the map contains the spelling reported by the operating system and lookups through `get` remain case-insensitive.

Concurrent environment mutation from foreign code has platform-defined behavior.

## 10. `std/time`

`std/time` exports durations, monotonic time, wall-clock time, and sleeping:

```lua
Duration.zero(): Duration
Duration.fromSeconds(value: u64): Duration
Duration.fromMilliseconds(value: u64): Duration
Duration.fromMicroseconds(value: u64): Duration
Duration.fromNanoseconds(value: u64): Duration
Duration.seconds(): u64
Duration.subsecondNanoseconds(): u32
Duration.checkedAdd(other: Duration): Duration?
Duration.checkedSub(other: Duration): Duration?

Instant.now(): Instant
Instant.elapsed(): Duration
Instant.durationSince(earlier: Instant): Duration?

SystemTime.now(): SystemTime
SystemTime.unixDuration(): Result<Duration, Error>

sleep(duration: Duration): Result<(), Error>
```

`Duration` is nonnegative and has nanosecond precision. Its stored resolution may be lower.

`Instant` uses a monotonic clock and has no calendar meaning. `durationSince` returns `nil` when `earlier` is later than `self`.

`SystemTime` can move backward. `unixDuration` measures from 1970-01-01T00:00:00Z and returns `Err` for an earlier time.

`sleep` blocks the current native thread for at least the requested duration unless interrupted. An interruption is `Err`.

## 11. `std/math`

`std/math` exports floating-point constants and functions:

```lua
pi: float
e: float
tau: float
infinity: float
nan: float

abs(value: float): float
min(left: float, right: float): float
max(left: float, right: float): float
clamp(value: float, low: float, high: float): float
floor(value: float): float
ceil(value: float): float
round(value: float): float
truncate(value: float): float
sqrt(value: float): float
cbrt(value: float): float
exp(value: float): float
log(value: float): float
log2(value: float): float
log10(value: float): float
sin(value: float): float
cos(value: float): float
tan(value: float): float
asin(value: float): float
acos(value: float): float
atan(value: float): float
atan2(y: float, x: float): float
```

Results follow IEEE 754. Domain errors produce NaN and overflow produces infinity. These functions do not return `Result` and do not inspect the process floating-point exception flags.

`clamp` traps when `low > high` or either bound is NaN. `min` and `max` return NaN when either operand is NaN.

## 12. `std/random`

`std/random` exports a deterministic generator and operating-system entropy:

```lua
Random.seeded(seed: u64): Random
Random.fromEntropy(): Result<Random, Error>
Random.nextU64(): u64
Random.nextBool(): bool
Random.nextFloat(): float
Random.int(low: int, high: int): int
Random.uint(low: u64, high: u64): u64
Random.fill(length: int): bytes
Random.shuffle<T>(values: List<T>): ()

secureBytes(length: int): Result<bytes, Error>
```

Two generators created with the same seed produce the same sequence on every target and every patch release of the same LuaR minor version.

`nextFloat` is in `[0.0, 1.0)`. `int` and `uint` use a half-open range and trap unless `low < high`. They avoid modulo bias.

`fill` and `secureBytes` trap for a negative length. `fill` uses the deterministic generator. `secureBytes` reads the operating system's cryptographic random source and returns `Err` where it is unavailable.

`shuffle` uses an unbiased Fisher-Yates shuffle.

## 13. `std/encoding`

`std/encoding` exports text and binary encodings:

```lua
utf8Encode(text: string): bytes
utf8Decode(data: bytes): Result<string, Error>

hexEncode(data: bytes): string
hexDecode(text: string): Result<bytes, Error>

base64Encode(data: bytes): string
base64Decode(text: string): Result<bytes, Error>
base64UrlEncode(data: bytes): string
base64UrlDecode(text: string): Result<bytes, Error>
```

`utf8Encode` copies the string's UTF-8 bytes. `utf8Decode` rejects malformed UTF-8, overlong forms, surrogates, and values above U+10FFFF.

`hexEncode` uses lowercase ASCII without separators. `hexDecode` accepts uppercase or lowercase and rejects whitespace, odd lengths, and non-hexadecimal characters.

Standard base64 uses the RFC 4648 alphabet and `=` padding. Its decoder requires canonical padding and rejects whitespace. The URL form uses `-` and `_`, emits no padding, and accepts either padded or unpadded canonical input.

## 14. `std/json`

`std/json` exports a JSON value model and typed encoding:

```lua
export enum Value
    Null
    Bool(bool)
    Number(float)
    String(string)
    Array(List<Value>)
    Object(Map<string, Value>)
end

parse(text: string): Result<Value, Error>
stringify(value: Value): string
stringifyPretty(value: Value): string

encode<T>(value: T): Result<string, Error> where T: Json
decode<T>(text: string): Result<T, Error> where T: Json
```

`Json` is the implementation generated by `@derive(Json)` and may be implemented explicitly. It covers booleans, strings, numeric primitives, optionals, lists, maps with string keys, structs, and enums.

`parse` accepts exactly one RFC 8259 JSON value followed by whitespace. Duplicate object names keep the last value. Invalid UTF-8 cannot occur because the input is a string.

`stringify` emits compact UTF-8 JSON. Object order is unspecified. It returns a valid JSON string for every `Value`; a non-finite `Number` becomes `null`.

`stringifyPretty` uses two spaces per nesting level and a trailing newline.

Typed decoding rejects missing required fields, unknown enum variants, values outside a numeric type's range, non-integral values for integer fields, and any shape that does not match `T`. Unknown struct fields are ignored unless the derive configuration rejects them.

## 15. `std/crypto`

`std/crypto` exports a small set of cryptographic building blocks:

```lua
sha256(data: bytes): bytes
sha512(data: bytes): bytes
hmacSha256(key: bytes, data: bytes): bytes
hmacSha512(key: bytes, data: bytes): bytes
constantTimeEqual(left: bytes, right: bytes): bool
randomBytes(length: int): Result<bytes, Error>
```

Hash and HMAC outputs are raw bytes in the algorithm's standard byte order. Use `std/encoding` for textual forms.

`constantTimeEqual` returns false for different lengths. Its work does not depend on the first differing byte.

`randomBytes` has the same entropy source and failure behavior as `std/random.secureBytes`.

The module does not expose home-grown encryption, password hashing, certificate validation, or key storage. Those require separate, versioned APIs backed by reviewed implementations.

## 16. `std/thread`

`std/thread` exports the `Send` and `Sync` marker interfaces defined by LR28 and native thread operations:

```lua
spawn<T>(work: () -> T): Result<Thread<T>, Error> where work: Send, T: Send
yield(): ()
currentId(): u64

Thread<T>.join(): Result<T, Error>
Thread<T>.detach(): ()
Thread<T>.isFinished(): bool
```

`spawn` starts one native thread and invokes `work` once. Captured values must satisfy `Send`.

`join` may be called once. It blocks until completion and returns `Err` if the thread terminates through an uncaught exception. `detach` releases the requirement to join. Dropping the last `Thread` handle detaches it.

`currentId` is unique among live threads in the process. It is not an operating-system thread identifier and may be reused after a thread exits.

## 17. `std/sync`

`std/sync` exports synchronization types for values shared between native threads:

```lua
Mutex.new<T>(value: T): Mutex<T> where T: Send
Mutex<T>.lock(): Result<MutexGuard<T>, Error>
MutexGuard<T>.get(): T
MutexGuard<T>.set(value: T): ()

RwLock.new<T>(value: T): RwLock<T> where T: Send + Sync
RwLock<T>.read(): Result<RwLockReadGuard<T>, Error>
RwLock<T>.write(): Result<RwLockWriteGuard<T>, Error>
RwLockReadGuard<T>.get(): T
RwLockWriteGuard<T>.get(): T
RwLockWriteGuard<T>.set(value: T): ()

Channel.new<T>(): (Sender<T>, Receiver<T>) where T: Send
Sender<T>.send(value: T): Result<(), T>
Receiver<T>.receive(): Result<T, Error>
Receiver<T>.tryReceive(): T?
```

Dropping a guard releases its lock. A guard does not implement `Send` or `Sync`. `get` copies a value type and shares a reference type according to LR31. A caller changes a copied value and passes it to `set` to replace the protected value. Read guards have no `set` method.

Lock acquisition is not reentrant. A callback that tries to acquire the same lock may deadlock. A panic releases the lock and makes the current call return `Err`; later acquisitions remain valid.

A channel has an unbounded queue. `send` returns `Err(value)` after every receiver is gone. `receive` blocks and returns `Err` after every sender is gone and the queue is empty. `tryReceive` returns `nil` when no value is ready, including a disconnected empty channel.

## 18. `std/net`

`std/net` exports IP addressing, DNS, TCP, and UDP:

```lua
export enum IpAddress
    V4(u8, u8, u8, u8)
    V6([u16; 8])
end

export struct SocketAddress
    address: IpAddress
    port: u16
end

resolve(host: string, port: u16): Result<List<SocketAddress>, Error>

TcpStream.connect(address: SocketAddress): Result<TcpStream, Error>
TcpStream.read(maximum: int): Result<bytes, Error>
TcpStream.write(data: bytes): Result<(), Error>
TcpStream.shutdown(): Result<(), Error>
TcpStream.peerAddress(): Result<SocketAddress, Error>
TcpStream.localAddress(): Result<SocketAddress, Error>

TcpListener.bind(address: SocketAddress): Result<TcpListener, Error>
TcpListener.accept(): Result<TcpStream, Error>
TcpListener.localAddress(): Result<SocketAddress, Error>

UdpSocket.bind(address: SocketAddress): Result<UdpSocket, Error>
UdpSocket.sendTo(data: bytes, address: SocketAddress): Result<int, Error>
UdpSocket.receiveFrom(maximum: int): Result<(bytes, SocketAddress), Error>
UdpSocket.localAddress(): Result<SocketAddress, Error>
```

`resolve` preserves the resolver's order and removes exact duplicates.

TCP reads return at most `maximum` bytes. An empty byte string means an orderly peer shutdown. TCP writes send the complete input or return `Err`.

UDP preserves datagram boundaries. `receiveFrom` truncates a datagram larger than `maximum`. A negative maximum traps.

Dropping the last handle closes its socket. Operations block the current thread. Async counterparts belong to `std/net/async` once the runtime can drive them without one thread per operation.

## 19. `std/http`

`std/http` exports HTTP/1.1 client and server APIs. It does not provide TLS by itself.

```lua
export enum Method
    Get
    Head
    Post
    Put
    Patch
    Delete
    Options
end

Headers.new(): Headers
Headers.get(name: string): string?
Headers.getAll(name: string): FrozenList<string>
Headers.set(name: string, value: string): ()
Headers.append(name: string, value: string): ()
Headers.remove(name: string): ()

export struct Request
    method: Method
    target: string
    headers: Headers
    body: bytes
end

export struct Response
    status: u16
    headers: Headers
    body: bytes
end

request(url: string, request: Request): Result<Response, Error>
serve(address: SocketAddress, handler: (Request) -> Response): Result<(), Error>
```

Header names compare case-insensitively. Values preserve insertion order. The library validates names and rejects carriage returns or line feeds in values.

`request` accepts `http` URLs. An `https` URL returns `Err` until a TLS transport is configured by a later API. Redirects are returned to the caller and are not followed automatically.

The response body has a configurable implementation limit. Exceeding it is `Err`; the library never grows an unbounded buffer from an untrusted peer.

`serve` accepts requests sequentially on the calling thread in v0. A handler response with an invalid status or headers becomes a 500 response and is logged through `std/log`.

## 20. `std/testing`

`std/testing` exports assertions and test-only filesystem helpers:

```lua
fail(message: string): never
equal<T>(actual: T, expected: T): () where T: Eq + Display
notEqual<T>(actual: T, expected: T): () where T: Eq + Display
some<T>(actual: T?): T
none<T>(actual: T?): ()
ok<T, E>(actual: Result<T, E>): T where E: Display
err<T, E>(actual: Result<T, E>): E where T: Display
panics(action: () -> ()): ()
tempDir(): Result<TempDir, Error>

TempDir.path(): string
```

These functions panic on an unmet assertion. Failure messages include the caller's source location where debug information is available.

`equal` and `notEqual` compare through `Eq` and format values through `Display` only when reporting failure.

`tempDir` creates a unique empty directory. Its finalizer removes that directory recursively. Cleanup failure is reported by the test runner.

The `@test` decorator and test discovery follow LR61. The runner executes tests in declaration order within a module and makes no ordering promise between modules. One test's panic does not stop later tests.

## 21. `std/log`

`std/log` exports structured severity and a process-wide logger:

```lua
export enum Level
    Trace
    Debug
    Info
    Warn
    Error
end

export struct Record
    level: Level
    target: string
    message: string
end

export interface Logger
    function enabled(self, level: Level, target: string): bool
    function write(self, record: Record): ()
    function flush(self): ()
end

setLogger(logger: Logger): Result<(), Error>
setLevel(level: Level): ()
log(level: Level, target: string, message: string): ()
trace(target: string, message: string): ()
debug(target: string, message: string): ()
info(target: string, message: string): ()
warn(target: string, message: string): ()
error(target: string, message: string): ()
flush(): ()
```

`setLogger` succeeds once per process. A later call returns `Err`. Before a logger is installed, records at `Info` or above go to standard error and lower levels are discarded.

`setLevel` sets the minimum enabled level. The logger's `enabled` method may filter further. Disabled records do not allocate their `Record`, but function arguments are evaluated before the call as required by LR55.

Logging never throws. A logger failure is discarded after its `write` or `flush` method returns.
