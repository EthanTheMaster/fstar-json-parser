# Overview
This project aims to implement a JSON parser that is formally verified to be compliant with [ECMA-404](https://www.json.org/json-en.html) and [RFC 8259](https://datatracker.ietf.org/doc/html/rfc8259). This JSON parser is written in `F*` and all correctness proofs are written in `F*`.

The language recognized by the parser is based off the grammar displayed at https://www.json.org/json-en.html. This grammar describes well-formed JSON strings as defined by [ECMA-404](https://www.json.org/json-en.html) and [RFC 8259](https://datatracker.ietf.org/doc/html/rfc8259).

This parser takes a (valid) UTF-8 encoded string and emits a parse tree for the input string. It does not assign any semantics to the parse tree. For example, the following actions are not currently supported:

- Indexing into JSON objects
- Indexing into JSON arrays
- Decoding a JSON string
- Decoding a JSON number into an integer for floating-point number
- etc

The downstream task of applying semantics to JSON values can however utilize the generated parse tree emitted by this parser.

The correctness properties of the parser are that

- All generated parse trees emitted by the parser can be generated from the JSON grammar and will expand into the original input string. Thus, all successfully parsed strings are well-formed JSON strings.
- All well-formed JSON strings, generated from some parse tree `T`, are parsed successfully into a parse tree matching `T`. Thus, all valid JSON strings will be accepted by the parser and faithfully reconstructed into a parse tree.

Put together, the parser will accept a string if and only if that string is a valid JSON string. These correctness properties have been proven and formally verified in `F*`.

# Project Structure
- `Json.Grammar.fst` encodes the JSON grammar into `F*` and defines how production rules of the grammar expand into a string.
- `Json.Parser.fst` defines the JSON parser and its associated correctness proofs 
    - Parsing function signature: `val parse_json (s: string) : option Json.Grammar.json`
    - Correctness proof signatures:

```fstar
val parse_json_soundness (s: string) : 
    Lemma (requires (Some? (parse_json s))) 
    (ensures (Json.Grammar.render_json (Some?.v (parse_json s)) == s)) 

val parse_json_completeness (js: Json.Grammar.json) :
  Lemma
  (ensures (
    Some? (parse_json (Json.Grammar.render_json js)) /\ 
    js == Some?.v (parse_json (Json.Grammar.render_json js))
  ))
```
- `Json.Main.fst` is an example main function calling the JSON parser on an input file emitting an exception, a message that the input string is invalid JSON, or the parsed JSON string.
- `ocaml_build.sh` is a quick script to generate OCAML code from the `F*` code to run inputs against.
- `test/` holds a test script running the generated OCAML binary against all test cases in https://github.com/nst/JSONTestSuite/. At the time of writing, all test points marked with `y` or `n` passes successfully.  

# Toolchain Used
```
> fstar.exe --version
F* 2025.02.06
platform=Darwin_arm64
compiler=OCaml 4.14.2
date=2025-02-07 02:04:06 -0700
commit=691c345c21d2a5b04db48d58e1fe47c6a5d3271e

> ocaml --version
The OCaml toplevel, version 4.14.2

> ocamlbuild --version
ocamlbuild 0.15.0
```