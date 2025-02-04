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

// Let S and S' be strings where S is a prefix of S'. That is S' = S + suffix for some suffix string.
// We say a parser is monotonic if the parser's result for S' is "larger" than S, for all such S and S'.
// A parser result R' is "larger" than another result R iff R is None or the length of the rendered
// parse tree for R' is at least the length of the rendered parse tree for R.
//
// Notice that monotonicity implies that extending a parseable string should never cause the parser to
// reject the extension.
let parser_monotonic
  (#production_rule: Type) 
  (parser: string -> option (parser_result production_rule))
  (renderer: production_rule -> string)
  (prefix suffix: string)
  =
  let parsed_prefix = parser prefix in
  let combined = prefix ^ suffix in
  let parsed = parser combined in
  match parsed_prefix with
    | Some res_prefix -> (
      match parsed with
        | Some res_combined -> String.strlen (renderer res_prefix.result) <= String.strlen (renderer res_combined.result)
        | None -> false
    )
    | None -> true



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

let postpend_empty_is_identity (s: string) : Lemma (ensures (s ^ "") == s) =
    list_of_concat s "";
    String.string_of_list_of_string (s ^ "");
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
  (requires Some? (parse_json_hex s))
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

let parse_json_escape (s: string) : option (parser_result json_escape) = 
  match String.list_of_string s with
    | [] -> None
    | c::tail -> 
      let is_escape_char = G.char_from_codepoint 0x22 = c || // '"'
                            G.char_from_codepoint 0x5C = c || // '\'
                            G.char_from_codepoint 0x62 = c || // 'b' 
                            G.char_from_codepoint 0x66 = c || // 'f'
                            G.char_from_codepoint 0x6E = c || // 'n'
                            G.char_from_codepoint 0x72 = c || // 'r'
                            G.char_from_codepoint 0x74 = c    // 't'
      in
      if is_escape_char then
        Some { result = Escape c; remainder = String.string_of_list tail }
      else
        // Attempt to parse as hex code
        match String.list_of_string s with
          | u::h1::h2::h3::h4::tail' -> 
              let h1_parse = parse_json_hex (G.char_to_str h1) in
              let h2_parse = parse_json_hex (G.char_to_str h2) in
              let h3_parse = parse_json_hex (G.char_to_str h3) in
              let h4_parse = parse_json_hex (G.char_to_str h4) in
              if (G.char_from_codepoint 0x75 = u) && (Some? h1_parse) && (Some? h2_parse) && (Some? h3_parse) && (Some? h4_parse) then
                Some {
                  result = HexCode u (Some?.v h1_parse).result (Some?.v h2_parse).result (Some?.v h3_parse).result (Some?.v h4_parse).result;
                  remainder = String.string_of_list tail'
                }
              else
                None
          | _ -> None

let parse_json_escape_soundness (s: string) :
  Lemma
  (requires (Some? (parse_json_escape s)))
  (ensures (parser_soundness parse_json_escape render_json_escape s)) 
  =
  let c::tail = String.list_of_string s in
  // Handle the escape char
  let is_escape_char = G.char_from_codepoint 0x22 = c || // '"'
                      G.char_from_codepoint 0x5C = c || // '\'
                      G.char_from_codepoint 0x62 = c || // 'b' 
                      G.char_from_codepoint 0x66 = c || // 'f'
                      G.char_from_codepoint 0x6E = c || // 'n'
                      G.char_from_codepoint 0x72 = c || // 'r'
                      G.char_from_codepoint 0x74 = c    // 't'
  in
  if is_escape_char then
    str_decompose s [c] tail
  else
    match String.list_of_string s with
      | u::h1::h2::h3::h4::tail' -> (
        // Prove decomposition
        assert(String.list_of_string s == ([u] @ [h1] @ [h2] @ [h3] @ [h4] @ tail'));
        str_decompose s [u] ([h1] @ [h2] @ [h3] @ [h4] @ tail');
        String.list_of_string_of_list ([h1] @ [h2] @ [h3] @ [h4] @ tail');
        str_decompose (String.string_of_list ([h1] @ [h2] @ [h3] @ [h4] @ tail')) [h1] ([h2] @ [h3] @ [h4] @ tail');
        String.list_of_string_of_list ([h2] @ [h3] @ [h4] @ tail');
        str_decompose (String.string_of_list ([h2] @ [h3] @ [h4] @ tail')) [h2] ([h3] @ [h4] @ tail');
        String.list_of_string_of_list ([h3] @ [h4] @ tail');
        str_decompose (String.string_of_list ([h3] @ [h4] @ tail')) [h3] ([h4] @ tail');
        String.list_of_string_of_list ([h4] @ tail');
        str_decompose (String.string_of_list ([h4] @ tail')) [h4] (tail');
        let u' = String.string_of_list [u] in
        let h1' = String.string_of_list [h1] in
        let h2' = String.string_of_list [h2] in
        let h3' = String.string_of_list [h3] in
        let h4' = String.string_of_list [h4] in
        let tail'_s = String.string_of_list tail' in
        assert(s == u' ^ h1' ^ h2' ^ h3' ^ h4' ^ tail'_s);
        // Use associative property to get parentheses to match the soundness theorem 
        str_concat_assoc h3' h4' tail'_s;
        str_concat_assoc h2' (h3' ^ h4') tail'_s;
        str_concat_assoc h1' (h2' ^ h3' ^ h4') tail'_s;
        str_concat_assoc u' (h1' ^ h2' ^ h3' ^ h4') tail'_s;
        assert(s == (u' ^ h1' ^ h2' ^ h3' ^ h4') ^ tail'_s);
        // Helper lemma to prove that each hi' where i=1,2,3,4 is equal to the rendered hex parsed result.
        let hex_parse_helper (h: char{Some? (parse_json_hex (G.char_to_str h))}) : Lemma (ensures (G.char_to_str h) == (render_json_hex (Some?.v (parse_json_hex (G.char_to_str h))).result)) =
          (
            parse_json_hex_soundness (G.char_to_str h);
            postpend_empty_is_identity (G.char_to_str h);
            list_of_string_of_list [h];
            str_decompose (G.char_to_str h) [h] []
          )
        in
        // Substitute hi' for i=1,2,3,4 in the decomposition to get soundness theorem
        hex_parse_helper h1;
        hex_parse_helper h2;
        hex_parse_helper h3;
        hex_parse_helper h4;
        ()
      )
      | _ -> ()

let parse_json_escape_completeness (escape: json_escape) :
  Lemma
  (ensures (parser_completeness parse_json_escape render_json_escape escape))
  =
  let rendered_escape = render_json_escape escape in
  match escape with
    | Escape c -> (
      String.list_of_string_of_list [c];
      str_decompose rendered_escape [c] [];
      assert((Some?.v (parse_json_escape rendered_escape)).result == escape);
      let c::tail = String.list_of_string rendered_escape in
      string_of_list_eq tail [];
      ()
    )
    | HexCode u h0 h1 h2 h3 -> (
      let u' = String.string_of_list [u] in
      // Helper lemma to prove that hex digits render into one character
      let hex_is_char (h: json_hex) : Lemma (ensures(match String.list_of_string (render_json_hex h) with | c::[] -> true | _ -> false)) = 
        match h with
          | HexDigit (DigitZero zero) -> String.list_of_string_of_list [zero]
          | HexDigit (DigitOneNine (OneNine c)) -> String.list_of_string_of_list [c]
          | HexAF c -> String.list_of_string_of_list [c]
      in
      hex_is_char h0;
      hex_is_char h1;
      hex_is_char h2;
      hex_is_char h3;
      let h0_s = render_json_hex h0 in
      let h1_s = render_json_hex h1 in
      let h2_s = render_json_hex h2 in
      let h3_s = render_json_hex h3 in
      let h0'::[] = String.list_of_string h0_s in
      let h1'::[] = String.list_of_string h1_s in
      let h2'::[] = String.list_of_string h2_s in
      let h3'::[] = String.list_of_string h3_s in
      String.list_of_string_of_list [u];
      String.list_of_string_of_list [h0'];
      String.list_of_string_of_list [h1'];
      String.list_of_string_of_list [h2'];
      String.list_of_string_of_list [h3'];
      assert (rendered_escape == u' ^ h0_s ^ h1_s ^ h2_s ^ h3_s);
      String.list_of_concat u' (h0_s ^ h1_s ^ h2_s ^ h3_s);
      String.list_of_concat h0_s (h1_s ^ h2_s ^ h3_s);
      String.list_of_concat h1_s (h2_s ^ h3_s);
      String.list_of_concat h2_s h3_s;
      // Successfully decomposed the rendered escape value into sequence of characters
      assert(String.list_of_string rendered_escape == [u] @ [h0'] @ [h1'] @ [h2'] @ [h3']);
      let u::h0'::h1'::h2'::h3'::tail = String.list_of_string rendered_escape in
      // Prove that all sub hex parses succeed and recover h0,h1,h2,h3
      String.string_of_list_of_string h0_s;
      String.string_of_list_of_string h1_s;
      String.string_of_list_of_string h2_s;
      String.string_of_list_of_string h3_s;
      assert((G.char_to_str h0') == render_json_hex h0);
      assert((G.char_to_str h1') == render_json_hex h1);
      assert((G.char_to_str h2') == render_json_hex h2);
      assert((G.char_to_str h3') == render_json_hex h3);
      // We now proved that input to hex parser effectively from a hex production rule allowing us to use completeness
      parse_json_hex_completeness h0;
      parse_json_hex_completeness h1;
      parse_json_hex_completeness h2;
      parse_json_hex_completeness h3
    )

let digit_len_one (d: json_digit) : Lemma (ensures (String.strlen (render_json_digit d)) == 1) =
  match d with
    | DigitZero c -> String.list_of_string_of_list [c]
    | DigitOneNine (OneNine c) -> String.list_of_string_of_list [c]

let rec parse_json_digits (s: string) : Tot (option (parser_result json_digits)) (decreases String.strlen s) =
  match parse_json_digit s with
    | Some { result=digit; remainder=remainder } -> (
      // Prove termination of recursive call by proving successfully digit parse yields a strictly smaller remainder
      parse_json_digit_soundness s; // Soundness provides a useable decomposition to reason about the length of remainder
      assert (s == render_json_digit digit ^ remainder);
      String.concat_length (render_json_digit digit) remainder;
      digit_len_one digit;
      match parse_json_digits remainder with
        | Some res -> Some {
          result = Digits digit res.result;
          remainder = res.remainder
        }
        | None -> Some {
          result = DigitsSingle digit;
          remainder = remainder
        }
    )
    | None -> None

let rec parse_json_digits_soundness (s: string) :
  Lemma
  (requires Some? (parse_json_digits s))
  (ensures parser_soundness parse_json_digits render_json_digits s)
  (decreases String.strlen s)
  =
  match parse_json_digit s with
    | Some { result=digit; remainder=remainder } -> (
      parse_json_digit_soundness s;
      // By digit soundness, s = render_json_digit digit + remainder
      match parse_json_digits remainder with
        | Some res -> (
          // Use same proof in parser to prove termination
          String.concat_length (render_json_digit digit) remainder;
          digit_len_one digit;
          parse_json_digits_soundness remainder;
          str_concat_assoc (render_json_digit digit) (render_json_digits res.result) res.remainder
        )
        | None -> ()
    )

let rec parse_json_digits_completeness (digits: json_digits) :
  Lemma
  (ensures (parser_completeness parse_json_digits render_json_digits digits))
  =
  match digits with
    | DigitsSingle digit -> (
      // This case reduces to using completeness of digit parser
      parse_json_digit_completeness digit;
      match parse_json_digit (render_json_digits digits) with
        | Some {result=digit; remainder=remainder} -> (
          assert(remainder == "");
          list_of_string_eq remainder "";
          assert(None? (parse_json_digit remainder));
          assert(None? (parse_json_digits remainder));
          ()
        )
    )
    | Digits digit digits' -> (
      let rendered_digits = render_json_digits digits in
      let digit_list = String.list_of_string (render_json_digit digit) in
      let digits'_list = String.list_of_string (render_json_digits digits') in
      // rendered_digits = (render_json_digit digit) + (render_json_digits digits')
      String.list_of_concat (render_json_digit digit) (render_json_digits digits');
      // Break of rendered digits into a list for easier analysis on the digit parsing
      assert(String.list_of_string rendered_digits == digit_list @ digits'_list);
      // Case analysis on digit to show that soundness assumption holds
      (
        match digit with
          | DigitZero c -> (
            // Give hint to FStar to prove that c comes from digit_list
            String.list_of_string_of_list [c];
            assert(Some? (parse_json_digit rendered_digits))
          )
          | DigitOneNine (OneNine c) -> (
            // Give hint to FStar to prove that c comes from digit_list
            String.list_of_string_of_list [c];
            assert(Some? (parse_json_digit rendered_digits))
          )
      );
      // Use soundness to decompose rendered digits to show that the remainder was generated by digits'
      // where we can then reapply completeness
      parse_json_digit_soundness rendered_digits;
      let Some { result=digit; remainder=remainder } = parse_json_digit rendered_digits in
      // Show that our two decompositions (digit_list w/ digits'_list and digit w/ remainder) are equivalent
      String.concat_injective (render_json_digit digit) (render_json_digit digit) remainder (render_json_digits digits');
      assert(remainder == render_json_digits digits');
      parse_json_digits_completeness digits';
      ()
    )

let parse_json_fraction (s: string) : parser_result json_fraction =
  match String.list_of_string s with
    | [] -> { result=NoFraction; remainder = s }
    | c::tail -> 
      if G.char_from_codepoint 0x2E = c then // '.'
        match parse_json_digits (String.string_of_list tail) with
          | Some parsed_digits -> { result = Fraction c parsed_digits.result; remainder = parsed_digits.remainder}
          | None -> { result=NoFraction; remainder = s }
      else
        { result=NoFraction; remainder = s }

let parse_json_fraction_soundness (s: string) :
  Lemma
  (ensures (parser_soundness (infallible_to_fallible_parser parse_json_fraction) render_json_fraction s))
  =
  match String.list_of_string s with
    | [] -> prepend_empty_is_identity s
    | c::tail -> 
      if G.char_from_codepoint 0x2E = c then // '.'
      (
        str_decompose s [c] tail;
        match parse_json_digits (String.string_of_list tail) with
          | Some parsed_digits -> (
            parse_json_digits_soundness (String.string_of_list tail);
            str_concat_assoc (String.string_of_list [c]) (render_json_digits parsed_digits.result) parsed_digits.remainder;
            ()
          )
          | None -> prepend_empty_is_identity s
      )
      else
        prepend_empty_is_identity s

let parse_json_fraction_completeness (fraction: json_fraction) :
  Lemma
  (ensures (parser_completeness (infallible_to_fallible_parser parse_json_fraction) render_json_fraction fraction))
  =
  let rendered_fraction = render_json_fraction fraction in
  match fraction with
    | NoFraction -> list_of_string_eq rendered_fraction ""
    | Fraction c digits -> (
      // rendered_fraction = (G.char_to_str c) + (rendered_json_digits digits)
      String.list_of_concat (G.char_to_str c) (render_json_digits digits);
      String.list_of_string_of_list [c];
      let c::tail = String.list_of_string rendered_fraction in
      str_decompose rendered_fraction [c] tail;
      String.concat_injective (G.char_to_str c) (G.char_to_str c) (render_json_digits digits) (String.string_of_list tail);
      assert (render_json_digits digits == String.string_of_list tail);
      parse_json_digits_completeness digits;
      ()
    )

let parse_json_exponent (s: string) : parser_result json_exponent =
  match String.list_of_string s with
    | [] -> { result=NoExponent; remainder=s }
    | c::tail -> 
      if (char_from_codepoint 0x65 = c) || (char_from_codepoint 0x45 = c) then
        let parsed_json_sign = parse_json_sign (String.string_of_list tail) in
        match parse_json_digits (parsed_json_sign.remainder) with
          | Some parsed_digits -> {
            result = Exponent c parsed_json_sign.result parsed_digits.result;
            remainder = parsed_digits.remainder
          }
          | None -> { result=NoExponent; remainder=s }
      else
        { result=NoExponent; remainder=s }

let parse_json_exponent_soundness (s: string) :
  Lemma
  (ensures parser_soundness (infallible_to_fallible_parser parse_json_exponent) render_json_exponent s)
  =
  match String.list_of_string s with
    | [] -> prepend_empty_is_identity s
    | c::tail -> 
      str_decompose s [c] tail;
      if (char_from_codepoint 0x65 = c) || (char_from_codepoint 0x45 = c) then
        let parsed_json_sign = parse_json_sign (String.string_of_list tail) in
        parse_json_sign_soundness (String.string_of_list tail);
        match parse_json_digits (parsed_json_sign.remainder) with
          | Some parsed_digits -> (
            parse_json_digits_soundness (parsed_json_sign.remainder);
            assert(s == (G.char_to_str c) ^ ((render_json_sign parsed_json_sign.result) ^ ((render_json_digits parsed_digits.result) ^ parsed_digits.remainder)));
            str_concat_assoc (render_json_sign parsed_json_sign.result) (render_json_digits parsed_digits.result) parsed_digits.remainder;
            str_concat_assoc (G.char_to_str c) ((render_json_sign parsed_json_sign.result) ^ (render_json_digits parsed_digits.result)) parsed_digits.remainder;
            ()
          )
          | None -> prepend_empty_is_identity s
      else
        prepend_empty_is_identity s

// Utility helper lemma showing that the first character of a string produced by json_digits starts for 0,1,2,...,9
let digits_start_character (digits: json_digits) :
  Lemma
  (ensures (
    let rendered_digits = render_json_digits digits in
    match String.list_of_string rendered_digits with
      | [] -> false
      | c::tail -> 
        let codepoint = U32.v (Char.u32_of_char c) in
        (0x30 <= codepoint /\ codepoint <= 0x39) // '0'-'9'
  ))
  =
  match digits with
    | DigitsSingle (DigitZero d) -> String.list_of_string_of_list [d]
    | DigitsSingle (DigitOneNine (OneNine d)) -> String.list_of_string_of_list [d]
    | Digits (DigitZero d) digits' -> (
      String.list_of_string_of_list [d];
      String.list_of_concat (G.char_to_str d) (render_json_digits digits')
    )
    | Digits (DigitOneNine (OneNine d)) digits' -> (
      String.list_of_string_of_list [d];
      String.list_of_concat (G.char_to_str d) (render_json_digits digits')
    )

let parse_json_exponent_completeness (exponent: json_exponent) :
  Lemma
  (ensures parser_completeness (infallible_to_fallible_parser parse_json_exponent) render_json_exponent exponent)
  =
  let rendered_exponent = render_json_exponent exponent in
  match exponent with
    | NoExponent -> list_of_string_eq rendered_exponent ""
    | Exponent c sign digits ->
      let rendered_sign = render_json_sign sign in
      let rendered_digits = render_json_digits digits in
      // rendered_exponent = (G.char_to_str c) + rendered_sign + rendered_digits
      String.list_of_concat (G.char_to_str c) (rendered_sign ^ rendered_digits);
      String.list_of_concat rendered_sign rendered_digits;
      list_of_string_of_list [c];
      let c::tail = String.list_of_string rendered_exponent in
      str_decompose rendered_exponent [c] tail;
      // string_of_list tail = rendered_sign + rendered_digits
      String.concat_injective (G.char_to_str c) (G.char_to_str c) (String.string_of_list tail) (rendered_sign ^ rendered_digits);
      String.list_of_string_of_list tail;
      match sign with
        | NoSign -> (
          // rendered_sign = ""
          prepend_empty_is_identity rendered_digits;
          assert(String.string_of_list tail == rendered_digits);
          // Prove that rendered_digits start with a character '0' to '9' making the sign parser yield NoSign
          digits_start_character digits;
          assert((parse_json_sign rendered_digits).result == NoSign);
          assert((parse_json_sign rendered_digits).remainder == rendered_digits);
          parse_json_digits_completeness digits;
          ()
        )
        | PlusMinus pm -> (
          String.list_of_string_of_list [pm];
          str_decompose (String.string_of_list tail) [pm] (String.list_of_string rendered_digits);
          let pm::tail' = tail in
          parse_json_sign_soundness (String.string_of_list tail);
          assert((parse_json_sign (String.string_of_list tail)).result == PlusMinus pm);
          assert((parse_json_sign (String.string_of_list tail)).remainder == String.string_of_list tail');
          String.concat_injective (G.char_to_str pm) (G.char_to_str pm) (parse_json_sign (String.string_of_list tail)).remainder rendered_digits;
          parse_json_digits_completeness digits;
          ()
        )

let parse_json_integer (s: string) : option (parser_result json_integer) =
  match String.list_of_string s with
    | [] -> None
    | c::tail -> if char_from_codepoint 0x2D = c then
      // Negative branch
      match parse_json_digit (String.string_of_list tail) with
        | Some ({ result=DigitZero d; remainder=remainder }) -> Some { result=IntNegDigit c (DigitZero d); remainder=remainder }
        | Some ({ result=DigitOneNine (OneNine d); remainder=remainder }) -> (
            match parse_json_digits remainder with
              | Some { result=digits; remainder=remainder } -> Some { result=IntNegDigits c (OneNine d) digits; remainder=remainder }
              | None -> Some { result=IntNegDigit c (DigitOneNine (OneNine d)); remainder=remainder }
        )
        | None -> None
    else
      // Non-negative branch
      match parse_json_digit s with
        | Some ({ result=DigitZero d; remainder=remainder }) -> Some { result=IntDigit (DigitZero d); remainder=remainder }
        | Some ({ result=DigitOneNine (OneNine d); remainder=remainder }) -> (
            match parse_json_digits remainder with
              | Some { result=digits; remainder=remainder } -> Some { result=IntDigits (OneNine d) digits; remainder=remainder }
              | None -> Some { result=IntDigit (DigitOneNine (OneNine d)); remainder=remainder }
        )
        | None -> None

let parse_json_integer_soundness (s: string) :
  Lemma
  (requires (Some? (parse_json_integer s)))
  (ensures (parser_soundness parse_json_integer render_json_integer s))
  =
  let c::tail = String.list_of_string s in
  if char_from_codepoint 0x2D = c then
  (
    str_decompose s [c] tail;
    parse_json_digit_soundness (String.string_of_list tail);
    match parse_json_digit (String.string_of_list tail) with
      | Some ({ result=DigitZero d; remainder=remainder }) -> str_concat_assoc (G.char_to_str c) (G.char_to_str d) remainder
      | Some ({ result=DigitOneNine (OneNine d); remainder=remainder }) -> (
        match parse_json_digits remainder with
          | Some { result=digits; remainder=remainder' } -> (
            parse_json_digits_soundness remainder;
            str_concat_assoc (G.char_to_str d) (render_json_digits digits) remainder';
            str_concat_assoc (G.char_to_str c) (G.char_to_str d ^ render_json_digits digits) remainder';
            ()
          )
          | None -> str_concat_assoc (G.char_to_str c) (G.char_to_str d) remainder
      )
  )
  else
    parse_json_digit_soundness s;
    match parse_json_digit s with
      | Some ({ result=DigitZero d; remainder=remainder }) -> ()
      | Some ({ result=DigitOneNine (OneNine d); remainder=remainder }) -> (
          match parse_json_digits remainder with
            | Some { result=digits; remainder=remainder' } -> (
              parse_json_digits_soundness remainder;
              str_concat_assoc (G.char_to_str d) (render_json_digits digits) remainder';
              ()
            )
            | None -> ()
      )
      | None -> ()

let parse_json_integer_completeness (integer: json_integer) :
  Lemma
  (ensures parser_completeness parse_json_integer render_json_integer integer)
  =
  let rendered_integer = render_json_integer integer in
  match integer with
    | IntDigit (DigitZero c) -> (
      list_of_string_of_list [c];
      parse_json_digit_completeness (DigitZero c);
      ()
    )
    | IntDigit (DigitOneNine (OneNine c)) -> (
      list_of_string_of_list [c];
      parse_json_digit_completeness (DigitOneNine (OneNine c));
      let Some { result=DigitOneNine (OneNine c); remainder = remainder } = parse_json_digit rendered_integer in
      list_of_string_eq remainder "";
      ()
    )
    | IntDigits (OneNine c) digits -> (
      String.list_of_concat (render_json_onenine (OneNine c)) (render_json_digits digits);
      String.list_of_string_of_list [c];
      let c::tail = String.list_of_string rendered_integer in
      let Some {result=DigitOneNine (OneNine c); remainder=remainder} = parse_json_digit rendered_integer in
      parse_json_digit_soundness rendered_integer;
      // Use the two decompositions of rendered_integers and prove equivalence
      String.concat_injective (G.char_to_str c) (G.char_to_str c) remainder (render_json_digits digits);
      parse_json_digits_completeness digits;
      ()
    )
    | IntNegDigit minus (DigitZero c) -> (
      String.list_of_concat (G.char_to_str minus) (G.char_to_str c);
      String.list_of_string_of_list [minus];
      String.list_of_string_of_list [c];
      parse_json_digit_completeness (DigitZero c);
      ()
    )
    | IntNegDigit minus (DigitOneNine (OneNine c)) -> (
      String.list_of_concat (G.char_to_str minus) (G.char_to_str c);
      String.list_of_string_of_list [minus];
      String.list_of_string_of_list [c];
      parse_json_digit_completeness (DigitOneNine (OneNine c));
      let minus::[c] = String.list_of_string rendered_integer in
      let Some { result=DigitOneNine (OneNine c); remainder = remainder } = parse_json_digit (String.string_of_list [c]) in
      list_of_string_eq remainder "";
      ()
    )
    | IntNegDigits minus (OneNine c) digits -> (
      String.list_of_concat (G.char_to_str minus) ((render_json_onenine (OneNine c)) ^ (render_json_digits digits));
      String.list_of_string_of_list [minus];
      String.list_of_string_of_list [c];
      let c'::tail = String.list_of_string rendered_integer in
      str_decompose rendered_integer [c'] tail;
      // Decompose and get back to the usual IntDigits case and replay that proof
      String.concat_injective (G.char_to_str minus) (G.char_to_str minus) (String.string_of_list tail) ((render_json_onenine (OneNine c)) ^ (render_json_digits digits));
      String.list_of_concat (render_json_onenine (OneNine c)) (render_json_digits digits);
      let c::tail' = tail  in
      let Some {result=DigitOneNine (OneNine c); remainder=remainder} = parse_json_digit (String.string_of_list tail) in
      parse_json_digit_soundness (String.string_of_list tail);
      String.concat_injective (G.char_to_str c) (G.char_to_str c) remainder (render_json_digits digits);
      parse_json_digits_completeness digits;
      ()
    )
