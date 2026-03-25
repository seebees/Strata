# Laurel Exception Support: Examples and Translator Contract

**Date:** 2026-03-25

## 1. The Translator Contract {#translator-contract}

The Laurel→Core translation proves:

> "If the Laurel program correctly uses `Throw` and `TryCatch`,
> the Core verification conditions are sound."

This proof rests on assumptions about what the language translators
produce. Each translator (Java→Laurel, Python→Laurel, etc.) MUST
honor these contracts when emitting exception constructs.

### Contract 1: Throw completeness {#contract-throw-completeness}

Every control flow path in the source language that raises/throws
an exception MUST be translated to a Laurel `Throw`.

If a translator omits a `Throw` for a path that can raise at
runtime, the verifier will treat that path as normal completion.
Postconditions will be checked on a path that actually throws —
this could produce false verification (unsound).

**Java example of violation:**
```java
// Source:
void foo(int x) {
    if (x < 0) throw new IllegalArgumentException();
}

// WRONG Laurel (omits the throw):
procedure foo(x: int) returns (result: Result<void>) {
    if (x < 0) { /* nothing */ }
    result := Success(void);
}
// Verifier thinks foo always succeeds — UNSOUND
```

### Contract 2: Throw fidelity {#contract-throw-fidelity}

The exception value in a `Throw` MUST correspond to the exception
constructed in the source language. The exception type MUST be
the correct type in the exception hierarchy.

If a translator emits the wrong exception type, catch dispatch
will be incorrect — a catch clause might match when it shouldn't,
or miss when it should match.

**Java example of violation:**
```java
// Source:
throw new IOException("disk full");

// WRONG Laurel (wrong type):
Throw(IllegalArgumentException("disk full"))
// catch (IOException e) won't match — UNSOUND
```

### Contract 3: TryCatch scope {#contract-trycatch-scope}

The body of a `TryCatch` MUST contain exactly the statements
that are lexically inside the source language's `try` block.
Catch clauses MUST list the correct exception types and bodies.

If a translator puts statements outside the `TryCatch` that
should be inside, exceptions from those statements won't be
caught. If it puts statements inside that should be outside,
exceptions will be incorrectly caught.

### Contract 4: Exception propagation {#contract-exception-propagation}

Every call to a method that can throw MUST be followed by a
check of the result. If the result is `Failure` and there is
no enclosing `TryCatch`, the caller MUST propagate the failure.

If a translator omits the propagation check, the caller will
continue executing with a `Failure` result as if it were
`Success` — using a garbage return value.

### Contract 5: Catch type ordering {#contract-catch-ordering}

Catch clauses MUST be emitted in the same order as the source
language. Java evaluates catch clauses top-to-bottom; the first
matching clause wins. Reordering could change which handler
executes.

---

## 2. Cross-Language Exception Patterns {#cross-language-patterns}

Different languages have different exception models. These
examples show how each maps to Laurel's `Throw`/`TryCatch`,
and what the translator must get right.

### 2.1 Java: Checked and unchecked exceptions {#java-patterns}

Java has two kinds of exceptions:
- **Checked** (`IOException`, `SQLException`): declared in `throws`,
  caller must catch or declare
- **Unchecked** (`RuntimeException` subclasses): any method can throw,
  no declaration required

Both map to Laurel `Throw` identically. The checked/unchecked
distinction is a Java compiler concern, not a verification concern.
The translator MUST emit `Throw` for both.

```java
// Java source:
void readFile(String path) throws IOException {
    if (path == null) throw new IllegalArgumentException("null path");
    if (!exists(path)) throw new IOException("not found");
    // ... read file ...
}
```

```
// Laurel:
procedure readFile(path: String) returns (result: Result<void>)
{
    if (path == null) {
        Throw(IllegalArgumentException("null path"));  // unchecked
    }
    if (!exists(path)) {
        Throw(IOException("not found"));                // checked
    }
    // ... read file ...
    result := Success(void);
}
```

**Translator responsibility:** Emit `Throw` for both checked and
unchecked exceptions. Do not skip unchecked exceptions just because
they lack a `throws` declaration.

### 2.2 Java: try/catch/finally {#java-trycatch}

```java
// Java source:
int process(String input) {
    int result = 0;
    try {
        result = parse(input);
        result = transform(result);
    } catch (NumberFormatException e) {
        result = -1;
    } catch (IllegalStateException e) {
        result = -2;
    } finally {
        log("done");
    }
    return result;
}
```

```
// Laurel:
procedure process(input: String) returns (result: Result<int>)
{
    var r := 0;
    TryCatch(
        body: {
            var parseResult := parse(input);
            // propagation check inserted by translator:
            if isFailure(parseResult) { Throw(parseResult.exception); }
            r := parseResult.value;

            var transformResult := transform(r);
            if isFailure(transformResult) { Throw(transformResult.exception); }
            r := transformResult.value;
        },
        catches: [
            CatchClause(NumberFormatException, "e", { r := -1; }),
            CatchClause(IllegalStateException, "e", { r := -2; }),
        ],
        finally: { log("done"); }
    );
    result := Success(r);
}
```

**Translator responsibility:**
- Insert propagation checks after every call to a method that
  returns `Result`
- Preserve catch clause ordering (NumberFormatException before
  IllegalStateException)
- Include the finally block

### 2.3 Python: try/except/else/finally {#python-patterns}

Python has `except` (like Java's `catch`), `else` (runs only if
no exception), and `finally`.

```python
# Python source:
def safe_divide(a, b):
    try:
        result = a / b
    except ZeroDivisionError as e:
        result = 0
    else:
        result = result * 2  # only if no exception
    finally:
        log("done")
    return result
```

```
// Laurel:
procedure safe_divide(a: Any, b: Any) returns (result: Result<Any>)
{
    var r;
    TryCatch(
        body: {
            r := divide(a, b);  // may throw ZeroDivisionError
            if isFailure(r) { Throw(r.exception); }
            // else block — only reached if body completes normally:
            r := multiply(r.value, 2);
        },
        catches: [
            CatchClause(ZeroDivisionError, "e", { r := Success(0); }),
        ],
        finally: { log("done"); }
    );
    result := r;
}
```

**Translator responsibility:**
- Python's `else` block is part of the try body (after all
  statements that might throw). The translator must place it
  inside the `TryCatch` body, after the last potentially-throwing
  statement.
- Python's `except Exception as e` binds the exception to `e`.
  The translator must emit the variable binding in the catch clause.

### 2.4 JavaScript: try/catch with single catch {#javascript-patterns}

JavaScript has a single `catch` clause (no type dispatch).
The handler receives the thrown value, which can be any type.

```javascript
// JavaScript source:
function parseJSON(text) {
    try {
        return JSON.parse(text);
    } catch (e) {
        return { error: e.message };
    }
}
```

```
// Laurel:
procedure parseJSON(text: String) returns (result: Result<Any>)
{
    TryCatch(
        body: {
            var parseResult := JSON_parse(text);
            if isFailure(parseResult) { Throw(parseResult.exception); }
            result := Success(parseResult.value);
        },
        catches: [
            CatchClause(Exception, "e", {
                result := Success(makeObject("error", e.message));
            }),
        ],
        finally: None
    );
}
```

**Translator responsibility:**
- JavaScript's single `catch` catches everything — translate as
  `CatchClause(Exception, ...)` (the root exception type).
- JavaScript can throw non-exception values (`throw "error"`).
  The translator must wrap these in an Exception type.

### 2.5 Go: Error returns (no exceptions) {#go-patterns}

Go doesn't have exceptions. Functions return `(value, error)` tuples.
This maps DIRECTLY to Laurel's `Result` type without needing
`Throw`/`TryCatch` at all.

```go
// Go source:
func readFile(path string) ([]byte, error) {
    if path == "" {
        return nil, fmt.Errorf("empty path")
    }
    data, err := os.ReadFile(path)
    if err != nil {
        return nil, err
    }
    return data, nil
}
```

```
// Laurel:
procedure readFile(path: String) returns (result: Result<ByteArray>)
{
    if (path == "") {
        result := Failure(Error("empty path"));
        return;
    }
    var readResult := os_ReadFile(path);
    if isFailure(readResult) {
        result := readResult;  // propagate
        return;
    }
    result := Success(readResult.value);
}
```

**Translator responsibility:**
- Go's `(value, error)` return pattern maps directly to `Result`.
  No `Throw`/`TryCatch` needed.
- The translator must recognize the `if err != nil { return ..., err }`
  pattern as error propagation.

This example validates the Result model: Go's explicit error handling
is exactly what the Laurel→Core translation produces from Java/Python
exceptions. The same verification conditions work for both.

