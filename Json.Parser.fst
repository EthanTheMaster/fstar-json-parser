module Json.Parser

open FStar.Char
open FStar.UInt32
open FStar.String
open FStar.Option
open FStar.List.Tot
open FStar.List.Tot.Properties
open Json.Grammar

module G = Json.Grammar
module Option = FStar.Option
module Char = FStar.Char
module U32 = FStar.UInt32
module String = FStar.String

type char = Char.char

let str_to_char (s: string{String.strlen s = 1}) : char = let c::_ = String.list_of_string s in c

// This type holds a successful parsing of a string which is decomposed in a parsed prefix and the remainder of the string
type parser_result a = {
  result: a;
  remainder: string;
}

// Correctness properties of a parser

// A parser is considered sound if whenever it successfully parses a string, then the parsing is valid in the
// sense that rendering the parse tree according to the production rule yields the original string.
let parser_soundness 
  (#production_rule: Type) 
  (parser: string -> (option (parser_result production_rule)))
  (renderer: production_rule -> string)
  (s: string)
  =
  match parser s with
    | Some parsed -> (s == renderer parsed.result ^ parsed.remainder)
    | None -> True

// A parser is considered complete if whenever it is presented with a string generated from a production rule,
// then the parser recovers the original production rule.
let parser_completeness
  (#production_rule: Type) 
  (parser: string -> option (parser_result production_rule))
  (renderer: production_rule -> string)
  (rule: production_rule)
  =
  let rendered_rule = renderer rule in
  let parsed = parser rendered_rule in
  (Some? parsed) /\ (Some?.v parsed).result == rule /\ (Some?.v parsed).remainder == ""

// Helper function to convert infallible parsers into a "fallible" parser
let infallible_to_fallible_parser (#production_rule: Type) (parser: string -> parser_result production_rule) = 
  fun (s:string) -> Some (parser s)
  

type nonempty_str = s:string{match String.list_of_string s with | c::tail -> true | _ -> false }

// Utility lemma to decompose a string into two list of characters
let str_decompose (s: string) (c1 c2: list char) : 
  Lemma 
  (requires (String.list_of_string s == c1 @ c2))
  (ensures (s == (String.string_of_list c1) ^ (String.string_of_list c2))) = 
  let c1_str = String.string_of_list c1 in
  let c2_str = String.string_of_list c2 in
  // s == string_of_list(list_of_string(s))
  String.string_of_list_of_string s;
  //   == string_of_list([c]) + string_of_list(tail) 
  String.list_of_concat c1_str c2_str;
  String.list_of_string_of_list c1;
  String.list_of_string_of_list c2;
  String.string_of_list_of_string (c1_str ^ c2_str)

// Utility lemma proving that chopping off the first character of a non-empty string decreases the string's length
let str_tail_decrease (s: nonempty_str) : 
  Lemma 
  (ensures (
    let c::tail = String.list_of_string s in 
    let tail_str = String.string_of_list tail in
    String.strlen tail_str < String.strlen s
    )
  ) =
  let c::tail = String.list_of_string s in
  // list_of_string s = [c] + tail
  assert(String.list_of_string s == [c] @ tail);
  // len(tail) = len(tail_str)
  String.list_of_string_of_list tail
  // len(s) = len(append([c], tail)) = len([c]) + len(tail)
  // len(tail_str) < len(s)

let list_of_string_eq (s1 s2: string): Lemma (requires s1 == s2) (ensures String.list_of_string s1 == String.list_of_string s2) = ()
let string_of_list_eq (l1 l2: list char): Lemma (requires l1 == l2) (ensures String.string_of_list l1 == String.string_of_list l2) = ()

// Utility lemma proving that string concatenation is associative
let str_concat_assoc (s1 s2 s3: string) : Lemma (ensures ((s1 ^ s2) ^ s3) == (s1 ^ (s2 ^ s3))) =
  let s1_chars = String.list_of_string s1 in
  let s2_chars = String.list_of_string s2 in
  let s3_chars = String.list_of_string s3 in
  // (s1 ^ s2) ^ s3 == string_of_list(list_of_string((s1 ^ s2) ^ s3))
  string_of_list_of_string ((s1 ^ s2) ^ s3);
  // list_of_string(s1 ^ s2) == list_of_string(s1) @ list_of_string(s2)
  list_of_concat s1 s2;
  // list_of_string((s1 ^ s2) ^ s3) == list_of_string(s1 ^ s2) @ list_of_string(s3)
  list_of_concat (s1 ^ s2) s3;
  FStar.List.Tot.Properties.append_assoc s1_chars s2_chars s3_chars;
  list_of_concat s1 (s2 ^ s3);
  list_of_concat s2 s3;
  string_of_list_of_string (s1 ^ (s2 ^ s3))


let rec parse_json_ws (s: string) : Tot (parser_result G.json_ws) (decreases (String.strlen s)) = 
  match String.list_of_string s with
  | [] -> { // Empty string
    result = G.NoWhitespace;
    remainder = s;
  }
  | c::tail -> 
    let is_whitespace = (c = G.char_from_codepoint 0x20) || (c = G.char_from_codepoint 0x0A) || (c = G.char_from_codepoint 0x0D) || (c = G.char_from_codepoint 0x09) in
    if is_whitespace then
      let tail_str = String.string_of_list tail in
      // Prove termination of recursive call
      str_tail_decrease s;
      let tail_parse = parse_json_ws tail_str in
      {
        result = G.Whitespace c tail_parse.result;
        remainder = tail_parse.remainder;
      }
    else
      { 
        result = G.NoWhitespace;
        remainder = s;
      }



// Prove correctness of whitespace parsing
let prepend_empty_is_identity (s: string) : Lemma (ensures ("" ^ s) == s) =
    // list_of_string("" + s) = list_of_string("") @ list_of_string(s) = list_of_string(s) 
    list_of_concat "" s;
    assert(String.list_of_string ("" ^ s) == String.list_of_string s);
    // "" + s = string_of_list(list_of_string("" + s)) = string_of_list(list_of_string(s)) == s
    String.string_of_list_of_string ("" ^ s);
    String.string_of_list_of_string s

let rec parse_json_ws_soundness (s: string) :
  Lemma 
  (ensures (parser_soundness (infallible_to_fallible_parser parse_json_ws) render_json_ws s))
  (decreases (String.strlen s)) =
  match String.list_of_string s with
    | [] -> 
      // By definition of parse_json_ws, it suffices to show s == "" + s
      prepend_empty_is_identity s
    | c::tail -> 
      let is_whitespace = (c = G.char_from_codepoint 0x20) || (c = G.char_from_codepoint 0x0A) || (c = G.char_from_codepoint 0x0D) || (c = G.char_from_codepoint 0x09) in
      if is_whitespace then
        let tail_str = String.string_of_list tail in
        let tail_parse = parse_json_ws tail_str in
        // Prove s == (c + tail_parse.result) + tail_parse.remainder
        list_of_string_of_list [c];
        //         == c + (tail_parse.result + tail_parse.remainder)
        str_concat_assoc (G.char_to_str c) (G.render_json_ws tail_parse.result) tail_parse.remainder;
        //         == c + tail_str [by induction]
        // Prove termination of recursive call
        str_tail_decrease s;
        parse_json_ws_soundness tail_str;
        // Prove s == string_of_list([c]) + tail_str
        str_decompose s [c] tail
      else
        prepend_empty_is_identity s


let rec parse_json_ws_completeness (ws: G.json_ws) :
  Lemma
  (ensures (parser_completeness (infallible_to_fallible_parser parse_json_ws) render_json_ws ws)) =
  let rendered_ws = G.render_json_ws ws in
  let parsed = parse_json_ws rendered_ws in
  match ws with
  | G.NoWhitespace -> ( 
    // Force F* into recognizing that match statement of parsing takes the empty list branch
    list_of_string_eq rendered_ws "";
    assert(parsed.result == NoWhitespace);
    assert(parsed.remainder == "")
  )
  | G.Whitespace c ws' -> (
    let rendered_ws' = render_json_ws ws' in
    // rendered_ws = c + render(ws')
    assert(rendered_ws == G.char_to_str c ^ rendered_ws');
    // list_of_string(rendered_ws) = [c] + list_of_string(render(ws'))
    String.list_of_concat (G.char_to_str c) rendered_ws';
    String.list_of_string_of_list [c];
    // parsed = {result = Whitespace c parse(render(ws')).result; remainder = parse(render(ws')).remainder}
    //        = {result = Whitespace c ws').result; remainder = ""}
    match String.list_of_string rendered_ws with
      // The naming of c is not ambiguous as they are (provably) the same c
      | c::parse_tail -> (
        let parse_tail_str = String.string_of_list parse_tail in
        assert(parse_tail == String.list_of_string rendered_ws');
        String.string_of_list_of_string rendered_ws';
        assert(parse_tail_str == rendered_ws');
        // Perform induction on parse_tail which is basically ws'
        parse_json_ws_completeness ws';
        assert(parsed.remainder == "");
        assert(parsed.result == Whitespace c ws');
        ()
      )
  )

let parse_json_sign (s: string) : Tot (parser_result G.json_sign) (decreases String.strlen s) = 
  match String.list_of_string s with
    | [] -> {
      result = NoSign;
      remainder = s
    }
    | c::tail -> 
      let plusminus = (c = G.char_from_codepoint 0x2B) || (c = G.char_from_codepoint 0x2D) in
      if plusminus then
        {
          result = PlusMinus c;
          remainder = String.string_of_list tail
        }
      else
        {
        result = NoSign;
        remainder = s
        }

// Prove correctness of json_sign parser
let parse_json_sign_soundness (s: string) : 
  Lemma
  (ensures (parser_soundness (infallible_to_fallible_parser parse_json_sign) render_json_sign s)) =
  match String.list_of_string s with
    | [] -> prepend_empty_is_identity s
    | c::tail -> 
      let plusminus = (c = G.char_from_codepoint 0x2B) || (c = G.char_from_codepoint 0x2D) in
      if plusminus then
        str_decompose s [c] tail
      else
        prepend_empty_is_identity s

let parse_json_sign_completeness (sign: json_sign) :
  Lemma
  (ensures (parser_completeness (infallible_to_fallible_parser parse_json_sign) render_json_sign sign)) =
  let rendered_sign = render_json_sign sign in
  let parsed = parse_json_sign rendered_sign in
  match sign with
  | G.NoSign -> list_of_string_eq rendered_sign ""
  | G.PlusMinus c -> (
    String.list_of_string_of_list [c];
    str_decompose rendered_sign [c] [];
    assert(parsed.result == PlusMinus c);
    let c::tail = String.list_of_string rendered_sign in
    assert(tail == []);
    assert(parsed.remainder == String.string_of_list tail);
    string_of_list_eq tail [];
    assert(parsed.remainder == String.string_of_list []);
    ()
  )
  
let parse_json_onenine (s: string) : option (parser_result json_onenine) =
  match String.list_of_string s with
    | [] -> None
    | c::tail -> 
      let codepoint = U32.v (Char.u32_of_char c) in
      let is_onenine = (0x31 <= codepoint && codepoint <= 0x39) in
      if is_onenine then
        Some ({ result = G.OneNine c; remainder = String.string_of_list tail})
      else
        None

let parse_json_onenine_soundness (s: string) :
  Lemma
  (requires Some? (parse_json_onenine s))
  (ensures (parser_soundness parse_json_onenine render_json_onenine s)) =
  // The branch in the parser is obvious
  let c::tail = String.list_of_string s in
  str_decompose s [c] tail;
  ()

let parse_json_onenine_completeness (onenine: json_onenine) :
  Lemma
  (ensures (parser_completeness parse_json_onenine render_json_onenine onenine))
  = 
  let rendered_onenine = render_json_onenine onenine in
  let parsed = parse_json_onenine rendered_onenine in
  let OneNine c = onenine in
  list_of_string_eq rendered_onenine (G.char_to_str c);
  String.list_of_string_of_list [c];
  assert(String.list_of_string rendered_onenine == [c]);
  let c::tail = String.list_of_string rendered_onenine in
  assert(Some? parsed);
  assert(onenine = (Some?.v parsed).result);
  string_of_list_eq tail [];
  assert((Some?.v parsed).remainder == "")

let parse_json_digit (s: string) : option (parser_result json_digit) =
  match String.list_of_string s with
    | [] -> None
    | c::tail -> 
      if char_from_codepoint 0x30 = c then
        // Zero
        Some { result = DigitZero c; remainder = String.string_of_list tail}
      else 
        match parse_json_onenine s with
          | Some res -> Some {
            result = DigitOneNine res.result;
            remainder = res.remainder
          }
          | None -> None

let parse_json_digit_soundness (s: string) :
  Lemma
  (requires Some? (parse_json_digit s))
  (ensures (parser_soundness parse_json_digit render_json_digit s)) 
  = 
  let c::tail = String.list_of_string s in
  str_decompose s [c] tail;
  match parse_json_onenine s with
    | Some res -> (
      parse_json_onenine_soundness s
    )
    | None -> ()

let parse_json_digit_completeness (digit: json_digit) :
  Lemma
  (ensures (parser_completeness parse_json_digit render_json_digit digit))
  =
  let rendered_digit = render_json_digit digit in
  match digit with 
    | DigitZero c -> (
      list_of_string_eq rendered_digit (G.char_to_str c);
      String.list_of_string_of_list [c];
      let c::tail = String.list_of_string rendered_digit in
      string_of_list_eq tail []
    )
    | DigitOneNine onenine -> (
      parse_json_onenine_completeness onenine
    )

let parse_json_hex (s: string) : option (parser_result json_hex) =
  match String.list_of_string s with
    | [] -> None
    | c::tail -> 
      let codepoint = U32.v (Char.u32_of_char c) in
      let is_af = (0x41 <= codepoint && codepoint <= 0x46) || (0x61 <= codepoint && codepoint <= 0x66) in
      if is_af then
        Some { result = HexAF c; remainder = String.string_of_list tail}
      else 
        match parse_json_digit s with
          | Some res -> Some {
            result = HexDigit res.result;
            remainder = res.remainder
          }
          | None -> None

let parse_json_hex_soundness (s: string) :
  Lemma
  (requires Some? (parse_json_digit s))
  (ensures (parser_soundness parse_json_hex render_json_hex s)) 
  = 
  let c::tail = String.list_of_string s in
  str_decompose s [c] tail;
  match parse_json_digit s with
    | Some res -> (
      parse_json_digit_soundness s
    )
    | None -> ()

let parse_json_hex_completeness (hex: json_hex) :
  Lemma
  (ensures (parser_completeness parse_json_hex render_json_hex hex))
  =
  let rendered_hex = render_json_hex hex in
  match hex with 
    | HexDigit digit -> (
      parse_json_digit_completeness digit
    )
    | HexAF c -> (
      list_of_string_eq rendered_hex (G.char_to_str c);
      String.list_of_string_of_list [c];
      let c::tail = String.list_of_string rendered_hex in
      string_of_list_eq tail []
    )