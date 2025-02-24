module Json.Parser

open FStar.Option
open FStar.List.Tot

module G = Json.Grammar
module Char = FStar.Char
module U32 = FStar.UInt32
module String = FStar.String
module List_Tot_Properties = FStar.List.Tot.Properties

type char = Char.char

// This type holds a successful parsing of a string which is decomposed in a parsed prefix and the remainder of the string
type parser_result a = {
  result: a;
  remainder: list char;
}

// Correctness properties of a parser

// A parser is considered sound if whenever it successfully parses a string, then the parsing is valid in the
// sense that rendering the parse tree according to the production rule yields the original string.
let parser_soundness 
  (#production_rule: Type) 
  (parser: list char -> (option (parser_result production_rule)))
  (renderer: production_rule -> string)
  (s: string)
  =
  match parser (String.list_of_string s) with
    | Some { result=result; remainder=remainder } -> (s == renderer result ^ String.string_of_list remainder)
    | None -> True

// A parser is considered complete if whenever it is presented with a string generated from a production rule,
// then the parser recovers the original production rule.
let parser_completeness
  (#production_rule: Type) 
  (parser: list char -> option (parser_result production_rule))
  (renderer: production_rule -> string)
  (rule: production_rule)
  =
  let rendered_rule = renderer rule in
  let parsed = parser (String.list_of_string rendered_rule) in
  (Some? parsed) /\ (Some?.v parsed).result == rule /\ (Some?.v parsed).remainder == []

// Helper function to convert infallible parsers into a "fallible" parser
let infallible_to_fallible_parser (#production_rule: Type) (parser: list char -> parser_result production_rule) = 
  fun (s:list char) -> Some (parser s)

// ### Utility lemmas and definitions ###

// Utility lemma proving that string concatenation is associative
let str_concat_assoc (s1 s2 s3: string) : Lemma (ensures ((s1 ^ s2) ^ s3) == (s1 ^ (s2 ^ s3))) =
  let s1_chars = String.list_of_string s1 in
  let s2_chars = String.list_of_string s2 in
  let s3_chars = String.list_of_string s3 in
  // (s1 ^ s2) ^ s3 == string_of_list(list_of_string((s1 ^ s2) ^ s3))
  String.string_of_list_of_string ((s1 ^ s2) ^ s3);
  // list_of_string(s1 ^ s2) == list_of_string(s1) @ list_of_string(s2)
  String.list_of_concat s1 s2;
  // list_of_string((s1 ^ s2) ^ s3) == list_of_string(s1 ^ s2) @ list_of_string(s3)
  String.list_of_concat (s1 ^ s2) s3;
  FStar.List.Tot.Properties.append_assoc s1_chars s2_chars s3_chars;
  String.list_of_concat s1 (s2 ^ s3);
  String.list_of_concat s2 s3;
  String.string_of_list_of_string (s1 ^ (s2 ^ s3))

// Utility lemma proving that chopping off the first character of a non-empty string decreases the string's length
type nonempty_str = s:string{match String.list_of_string s with | c::tail -> true | _ -> false }
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

let prepend_empty_is_identity (s: string) : Lemma (ensures ("" ^ s) == s) =
    // list_of_string("" + s) = list_of_string("") @ list_of_string(s) = list_of_string(s) 
    String.list_of_concat "" s;
    assert(String.list_of_string ("" ^ s) == String.list_of_string s);
    // "" + s = string_of_list(list_of_string("" + s)) = string_of_list(list_of_string(s)) == s
    String.string_of_list_of_string ("" ^ s);
    String.string_of_list_of_string s

let postpend_empty_is_identity (s: string) : Lemma (ensures (s ^ "") == s) =
    String.list_of_concat s "";
    String.string_of_list_of_string (s ^ "");
    String.string_of_list_of_string s

let list_of_string_eq (s1 s2: string): Lemma (requires s1 == s2) (ensures String.list_of_string s1 == String.list_of_string s2) = ()
let string_of_list_eq (l1 l2: list char): Lemma (requires l1 == l2) (ensures String.string_of_list l1 == String.string_of_list l2) = ()

let empty_iff_len_zero (s: string): Lemma (ensures (s == "" <==> String.strlen s == 0)) = 
  introduce s == "" ==> String.strlen s == 0
  with pf_s_empty. 
  (
    String.list_of_string_of_list [];
    list_of_string_eq s (String.string_of_list [])
  );
  introduce String.strlen s == 0 ==> s == ""
  with pf_s_len_zero. 
  (
    assert(String.list_of_string s == []);
    String.string_of_list_of_string s;
    string_of_list_eq [] (String.list_of_string s)
  )

let is_char_whitespace (c: char) = (c = G.char_from_codepoint 0x20) || (c = G.char_from_codepoint 0x0A) || (c = G.char_from_codepoint 0x0D) || (c = G.char_from_codepoint 0x09)

let hex_is_char (h: G.json_hex) : Lemma (ensures(match String.list_of_string (G.render_json_hex h) with | c::[] -> true | _ -> false)) = 
  match h with
    | G.HexDigit (G.DigitZero zero) -> String.list_of_string_of_list [zero]
    | G.HexDigit (G.DigitOneNine (G.OneNine c)) -> String.list_of_string_of_list [c]
    | G.HexAF c -> String.list_of_string_of_list [c]

let digit_len_one (d: G.json_digit) : Lemma (ensures (String.strlen (G.render_json_digit d)) == 1) =
  match d with
    | G.DigitZero c -> String.list_of_string_of_list [c]
    | G.DigitOneNine (G.OneNine c) -> String.list_of_string_of_list [c]

// Utility helper lemma showing that the first character of a string produced by json_digits starts for 0,1,2,...,9
let digits_start_character (digits: G.json_digits) :
  Lemma
  (ensures (
    let rendered_digits = G.render_json_digits digits in
    match String.list_of_string rendered_digits with
      | [] -> false
      | c::tail -> 
        let codepoint = U32.v (Char.u32_of_char c) in
        (0x30 <= codepoint /\ codepoint <= 0x39) // '0'-'9'
  ))
  =
  match digits with
    | G.DigitsSingle (G.DigitZero d) -> String.list_of_string_of_list [d]
    | G.DigitsSingle (G.DigitOneNine (G.OneNine d)) -> String.list_of_string_of_list [d]
    | G.Digits (G.DigitZero d) digits' -> (
      String.list_of_string_of_list [d];
      String.list_of_concat (G.char_to_str d) (G.render_json_digits digits')
    )
    | G.Digits (G.DigitOneNine (G.OneNine d)) digits' -> (
      String.list_of_string_of_list [d];
      String.list_of_concat (G.char_to_str d) (G.render_json_digits digits')
    )

let is_digit_char (c: char) = 
  let codepoint = U32.v (Char.u32_of_char c) in
  (0x30 <= codepoint && codepoint <= 0x39) // '0' to '9'

let matching_parse_result #production_rule (s1 s2: string) (parser: list char -> option (parser_result production_rule)) = 
  let parse1 = parser (String.list_of_string s1) in
  let parse2 = parser (String.list_of_string s2) in
  match parse1 with
    | None -> parse1 == parse2
    | Some { result=result; remainder=_ } -> (Some? parse2) /\ (Some?.v parse2).result == result

let that_first_char_of (s: string) (cond: char -> bool) = 
  match String.list_of_string s with
    | [] -> true
    | c::_ -> cond c

let json_fraction_empty_or_period (fraction: G.json_fraction) : 
  Lemma
  (ensures (
    let rendered_fraction = G.render_json_fraction fraction in
    match String.list_of_string rendered_fraction with
      | [] -> true
      | c::_ -> c = G.char_from_codepoint 0x2E
  ))
  =
  match fraction with
    | G.NoFraction ->  list_of_string_eq "" (G.render_json_fraction fraction)
    | G.Fraction c digits -> (
        String.list_of_concat (G.char_to_str c) (G.render_json_digits digits);
        String.list_of_string_of_list [c]
    )

let json_exponent_empty_or_e (exponent: G.json_exponent) : 
  Lemma
  (ensures (
    let rendered_exponent = G.render_json_exponent exponent in
    match String.list_of_string rendered_exponent with
      | [] -> true
      | c::_ -> (c = G.char_from_codepoint 0x65) \/ (c = G.char_from_codepoint 0x45)
  ))
  =
  match exponent with
    | G.NoExponent -> list_of_string_eq "" (G.render_json_exponent exponent)
    | G.Exponent c sign digits -> (
      str_concat_assoc (G.char_to_str c) (G.render_json_sign sign) (G.render_json_digits digits);
      String.list_of_concat (G.char_to_str c) ((G.render_json_sign sign) ^ (G.render_json_digits digits));
      String.list_of_string_of_list [c]
    )

// Utility lemma stating that the start character of s1 is the same as s1^s2 for any strings s1 and s2, assuming s1 has a starting character
let start_character_concat (s1 s2: string) :
  Lemma
  (ensures 
    (that_first_char_of s1 (fun c1 -> that_first_char_of (s1 ^ s2) (fun c2 -> c1 = c2))) /\
    // Technical condition to make life easier by telling Fstar that the inner that_first_char_of is not vacuously true
    // when s1 is non-empty. 
    (not(String.list_of_string s1 = []) ==> not(String.list_of_string (s1 ^ s2) = []))
  )
  =
  match String.list_of_string s1 with
    | [] -> ()
    | c::tail -> (
      String.list_of_string_of_list [c];
      str_decompose s1 [c] tail;
      str_concat_assoc (G.char_to_str c) (String.string_of_list tail) s2;
      String.list_of_concat (G.char_to_str c) ((String.string_of_list tail) ^ s2)
    )

// Helper function to detect if a character can extend a parsed json_number
let is_char_not_json_number_extendable (c: char) = 
    // Combine requirements of exponent, digits, fraction termination
    not (is_digit_char c) && 
    not (c = G.char_from_codepoint 0x2E) && 
    not (c = G.char_from_codepoint 0x65) && 
    not (c = G.char_from_codepoint 0x45) &&
    not (c = G.char_from_codepoint 0x2B) &&
    not (c = G.char_from_codepoint 0x2D)

// Utility lemma indicating the a json_number starts with a negative sign or a digit
let json_number_start_character (number: G.json_number) : 
  Lemma 
  (ensures (
    that_first_char_of (G.render_json_number number) (fun c -> 
      is_digit_char c ||
      c = G.char_from_codepoint 0x2D // '-'
      )
    ) /\ not(String.list_of_string (G.render_json_number number) = []))
  =
  let G.Number integer fraction exponent = number in
  String.list_of_concat (G.render_json_integer integer) ((G.render_json_fraction fraction) ^ (G.render_json_exponent exponent));
  match integer with
    | G.IntDigit digit -> digits_start_character (G.DigitsSingle digit)
    | G.IntDigits onenine digits -> (
      String.list_of_concat (G.render_json_onenine onenine) (G.render_json_digits digits);
      digits_start_character (G.DigitsSingle (G.DigitOneNine onenine))
    )
    | G.IntNegDigit neg digit -> (
      String.list_of_string_of_list [neg];
      String.list_of_concat (G.char_to_str neg) (G.render_json_digit digit)
    )
    | G.IntNegDigits neg onenine digits -> (
      String.list_of_string_of_list [neg];
      str_concat_assoc (G.char_to_str neg) (G.render_json_onenine onenine) (G.render_json_digits digits);
      String.list_of_concat (G.char_to_str neg) ((G.render_json_onenine onenine) ^ (G.render_json_digits digits))
    )

let character_render_length (character: G.json_character) :
  Lemma
  (ensures (
    let rendered_character = G.render_json_character character in
    let length = String.strlen rendered_character in
    length == 1 \/ length == 2 \/ length == 6
  ))
  =
  match character with
    | G.Character c -> String.list_of_string_of_list [c]
    | G.EscapedCharacter c (G.Escape c') -> (
      String.list_of_string_of_list [c];
      String.list_of_string_of_list [c'];
      String.list_of_concat (G.char_to_str c) (G.char_to_str c')
    )
    | G.EscapedCharacter c (G.HexCode c' h1 h2 h3 h4) -> (
      let hex_length_one (h: G.json_hex) : Lemma (ensures (String.strlen (G.render_json_hex h) == 1)) = 
        match h with
          | G.HexDigit d -> digit_len_one d
          | G.HexAF c -> String.list_of_string_of_list [c]
      in
      String.list_of_string_of_list [c];
      String.list_of_string_of_list [c'];
      hex_length_one h1;
      hex_length_one h2;
      hex_length_one h3;
      hex_length_one h4;
      let rendered_h1 = G.render_json_hex h1 in
      let rendered_h2 = G.render_json_hex h2 in
      let rendered_h3 = G.render_json_hex h3 in
      let rendered_h4 = G.render_json_hex h4 in
      String.concat_length (G.char_to_str c) ((G.char_to_str c') ^ rendered_h1 ^ rendered_h2 ^ rendered_h3 ^ rendered_h4);
      String.concat_length (G.char_to_str c') (rendered_h1 ^ rendered_h2 ^ rendered_h3 ^ rendered_h4);
      String.concat_length rendered_h1 (rendered_h2 ^ rendered_h3 ^ rendered_h4);
      String.concat_length rendered_h2 (rendered_h3 ^ rendered_h4);
      String.concat_length rendered_h3 rendered_h4
    )

// Helper lemma stating that json strings will always render to a nonempty string starting with a '"'
let json_string_start_character (s: G.json_string) :
  Lemma
  (ensures (
    let rendered_string = G.render_json_string s in
    that_first_char_of rendered_string (fun c -> c = G.char_from_codepoint 0x22) /\ // '"'
    not (String.list_of_string rendered_string = [])
  ))
  =
  let G.String c0 chars c1 = s in
  String.list_of_concat (G.char_to_str c0) ((G.render_json_characters chars) ^ (G.char_to_str c1));
  String.list_of_string_of_list [c0]

// Helper lemma describe the start characters of a rendered json_value
let json_value_start_character (value: G.json_value) :
  Lemma
  (ensures (
    that_first_char_of (G.render_json_value value) (fun c -> 
      c = (G.char_from_codepoint 0x7B) || // '{'
      c = (G.char_from_codepoint 0x5B) || // '['
      c = (G.char_from_codepoint 0x22) || // '"'
      c = (G.char_from_codepoint 0x22) || // '"'
      is_digit_char c || 
      c = (G.char_from_codepoint 0x2D) || // "-"
      c = (G.char_from_codepoint 0x74) || // "t"
      c = (G.char_from_codepoint 0x66) || // "f"
      c = (G.char_from_codepoint 0x6E) // "n"
    )
    &&
    not(String.list_of_string (G.render_json_value value) = [])
  ))
  =
  match value with
    | G.ObjectValue object -> (
      match object with
        | G.EmptyObject c0 ws c1 -> (
          String.list_of_string_of_list [c0];
          String.list_of_concat (G.char_to_str c0) ((G.render_json_ws ws) ^ (G.char_to_str c1))
        )
        | G.Object c0 members c1 -> (
          String.list_of_string_of_list [c0];
          String.list_of_concat (G.char_to_str c0) ((G.render_json_members members) ^ (G.char_to_str c1))
        )
    )
    | G.ArrayValue array -> (
      match array with
        | G.EmptyArray c0 ws c1 -> (
          String.list_of_string_of_list [c0];
          String.list_of_concat (G.char_to_str c0) ((G.render_json_ws ws) ^ (G.char_to_str c1))
        )
        | G.Array c0 elems c1 -> (
          String.list_of_string_of_list [c0];
          String.list_of_concat (G.char_to_str c0) ((G.render_json_elements elems) ^ (G.char_to_str c1))
        )
    )
    | G.StringValue str -> json_string_start_character str
    | G.NumberValue number -> json_number_start_character number
    | G.BooleanValue s -> (
      if s = "true" then
      (
        String.list_of_string_of_list ['t';'r';'u';'e'];
        list_of_string_eq s (String.string_of_list ['t';'r';'u';'e'])
      )
      else
      (
        String.list_of_string_of_list ['f';'a';'l';'s';'e'];
        list_of_string_eq s (String.string_of_list ['f';'a';'l';'s';'e'])
      )
    )
    | G.NullValue s -> (
      String.list_of_string_of_list ['n';'u';'l';'l'];
      list_of_string_eq s (String.string_of_list ['n';'u';'l';'l'])
    )

// ### Parsing logic and proofs ###

let rec parse_json_ws (s: list char) : Tot (parser_result G.json_ws) = 
  match s with
  | [] -> { // Empty string
    result = G.NoWhitespace;
    remainder = s;
  }
  | c::tail -> 
    let is_whitespace = is_char_whitespace c in
    if is_whitespace then
      let tail_parse = parse_json_ws tail in
      {
        result = G.Whitespace c tail_parse.result;
        remainder = tail_parse.remainder;
      }
    else
      { 
        result = G.NoWhitespace;
        remainder = s;
      }

let rec parse_json_ws_soundness (s: string) :
  Lemma 
  (ensures (parser_soundness (infallible_to_fallible_parser parse_json_ws) G.render_json_ws s))
  (decreases (String.strlen s)) =
  String.string_of_list_of_string s;
  match String.list_of_string s with
    | [] -> 
      // By definition of parse_json_ws, it suffices to show s == "" + s
      prepend_empty_is_identity s
    | c::tail -> 
      let is_whitespace = is_char_whitespace c in
      if is_whitespace then
        let tail_str = String.string_of_list tail in
        let tail_parse = parse_json_ws tail in
        // Prove s == (c + tail_parse.result) + tail_parse.remainder
        String.list_of_string_of_list [c];
        String.list_of_string_of_list tail;
        //         == c + (tail_parse.result + tail_parse.remainder)
        str_concat_assoc (G.char_to_str c) (G.render_json_ws tail_parse.result) (String.string_of_list tail_parse.remainder);
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
  (ensures (parser_completeness (infallible_to_fallible_parser parse_json_ws) G.render_json_ws ws)) =
  let rendered_ws = G.render_json_ws ws in
  let parsed = parse_json_ws (String.list_of_string rendered_ws) in
  match ws with
  | G.NoWhitespace -> ( 
    // Force F* into recognizing that match statement of parsing takes the empty list branch
    list_of_string_eq rendered_ws "";
    assert(parsed.result == G.NoWhitespace);
    assert(parsed.remainder == [])
  )
  | G.Whitespace c ws' -> (
    let rendered_ws' = G.render_json_ws ws' in
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
        assert(parse_tail == String.list_of_string rendered_ws');
        String.string_of_list_of_string rendered_ws';
        // Perform induction on parse_tail which is basically ws'
        parse_json_ws_completeness ws';
        assert(parsed.remainder == []);
        assert(parsed.result == G.Whitespace c ws');
        ()
      )
  )

let parse_json_sign (s: list char) : Tot (parser_result G.json_sign) = 
  match s with
    | [] -> {
      result = G.NoSign;
      remainder = s
    }
    | c::tail -> 
      let plusminus = (c = G.char_from_codepoint 0x2B) || (c = G.char_from_codepoint 0x2D) in
      if plusminus then
        {
          result = G.PlusMinus c;
          remainder = tail
        }
      else
        {
        result = G.NoSign;
        remainder = s
        }

let parse_json_sign_soundness (s: string) : 
  Lemma
  (ensures (parser_soundness (infallible_to_fallible_parser parse_json_sign) G.render_json_sign s)) =
  String.string_of_list_of_string s;
  match String.list_of_string s with
    | [] -> prepend_empty_is_identity s
    | c::tail -> 
      let plusminus = (c = G.char_from_codepoint 0x2B) || (c = G.char_from_codepoint 0x2D) in
      if plusminus then
        str_decompose s [c] tail
      else
        prepend_empty_is_identity s

let parse_json_sign_completeness (sign: G.json_sign) :
  Lemma
  (ensures (parser_completeness (infallible_to_fallible_parser parse_json_sign) G.render_json_sign sign)) =
  let rendered_sign = G.render_json_sign sign in
  let parsed = parse_json_sign (String.list_of_string rendered_sign) in
  match sign with
  | G.NoSign -> list_of_string_eq rendered_sign ""
  | G.PlusMinus c -> (
    String.list_of_string_of_list [c];
    str_decompose rendered_sign [c] [];
    assert(parsed.result == G.PlusMinus c);
    let c::tail = String.list_of_string rendered_sign in
    assert(tail == []);
    assert(parsed.remainder == tail);
    string_of_list_eq tail [];
    assert(parsed.remainder == [])
  )

let parse_json_onenine (s: list char) : option (parser_result G.json_onenine) =
  match s with
    | [] -> None
    | c::tail -> 
      let codepoint = U32.v (Char.u32_of_char c) in
      let is_onenine = (0x31 <= codepoint && codepoint <= 0x39) in
      if is_onenine then
        Some ({ result = G.OneNine c; remainder = tail})
      else
        None

let parse_json_onenine_soundness (s: string) :
  Lemma
  (requires Some? (parse_json_onenine (String.list_of_string s)))
  (ensures (parser_soundness parse_json_onenine G.render_json_onenine s)) =
  // The branch in the parser is obvious
  let c::tail = String.list_of_string s in
  str_decompose s [c] tail

let parse_json_onenine_completeness (onenine: G.json_onenine) :
  Lemma
  (ensures (parser_completeness parse_json_onenine G.render_json_onenine onenine))
  = 
  let rendered_onenine = G.render_json_onenine onenine in
  let parsed = parse_json_onenine (String.list_of_string rendered_onenine) in
  let G.OneNine c = onenine in
  list_of_string_eq rendered_onenine (G.char_to_str c);
  String.list_of_string_of_list [c];
  assert(String.list_of_string rendered_onenine == [c]);
  let c::tail = String.list_of_string rendered_onenine in
  assert(Some? parsed);
  assert(onenine = (Some?.v parsed).result);
  string_of_list_eq tail [];
  assert((Some?.v parsed).remainder == [])

let parse_json_digit (s: list char) : option (parser_result G.json_digit) =
  match s with
    | [] -> None
    | c::tail -> 
      if G.char_from_codepoint 0x30 = c then
        // Zero
        Some { result = G.DigitZero c; remainder = tail}
      else 
        match parse_json_onenine s with
          | Some res -> Some {
            result = G.DigitOneNine res.result;
            remainder = res.remainder
          }
          | None -> None
  
let parse_json_digit_soundness (s: string) :
  Lemma
  (requires Some? (parse_json_digit (String.list_of_string s)))
  (ensures (parser_soundness parse_json_digit G.render_json_digit s)) 
  = 
  let c::tail = String.list_of_string s in
  str_decompose s [c] tail;
  match parse_json_onenine (String.list_of_string s) with
    | Some res -> (
      parse_json_onenine_soundness s
    )
    | None -> ()

let parse_json_digit_completeness (digit: G.json_digit) :
  Lemma
  (ensures (parser_completeness parse_json_digit G.render_json_digit digit))
  =
  let rendered_digit = G.render_json_digit digit in
  match digit with 
    | G.DigitZero c -> (
      list_of_string_eq rendered_digit (G.char_to_str c);
      String.list_of_string_of_list [c];
      let c::tail = String.list_of_string rendered_digit in
      string_of_list_eq tail []
    )
    | G.DigitOneNine onenine -> (
      parse_json_onenine_completeness onenine
    )

let parse_json_hex (s: list char) : option (parser_result G.json_hex) =
  match s with
    | [] -> None
    | c::tail -> 
      let codepoint = U32.v (Char.u32_of_char c) in
      let is_af = (0x41 <= codepoint && codepoint <= 0x46) || (0x61 <= codepoint && codepoint <= 0x66) in
      if is_af then
        Some { result = G.HexAF c; remainder = tail}
      else 
        match parse_json_digit s with
          | Some res -> Some {
            result = G.HexDigit res.result;
            remainder = res.remainder
          }
          | None -> None

let parse_json_hex_soundness (s: string) :
  Lemma
  (requires Some? (parse_json_hex (String.list_of_string s)))
  (ensures (parser_soundness parse_json_hex G.render_json_hex s)) 
  = 
  let c::tail = String.list_of_string s in
  str_decompose s [c] tail;
  match parse_json_digit (String.list_of_string s) with
    | Some res -> (
      parse_json_digit_soundness s
    )
    | None -> ()

let parse_json_hex_completeness (hex: G.json_hex) :
  Lemma
  (ensures (parser_completeness parse_json_hex G.render_json_hex hex))
  =
  let rendered_hex = G.render_json_hex hex in
  match hex with 
    | G.HexDigit digit -> (
      parse_json_digit_completeness digit
    )
    | G.HexAF c -> (
      list_of_string_eq rendered_hex (G.char_to_str c);
      String.list_of_string_of_list [c];
      let c::tail = String.list_of_string rendered_hex in
      string_of_list_eq tail []
    )

let parse_json_escape (s: list char) : option (parser_result G.json_escape) = 
  match s with
    | [] -> None
    | c::tail -> 
      let is_escape_char = G.char_from_codepoint 0x22 = c || // '"'
                            G.char_from_codepoint 0x5C = c || // '\'
                            G.char_from_codepoint 0x2F = c || // '/'
                            G.char_from_codepoint 0x62 = c || // 'b' 
                            G.char_from_codepoint 0x66 = c || // 'f'
                            G.char_from_codepoint 0x6E = c || // 'n'
                            G.char_from_codepoint 0x72 = c || // 'r'
                            G.char_from_codepoint 0x74 = c    // 't'
      in
      if is_escape_char then
        Some { result = G.Escape c; remainder = tail }
      else
        // Attempt to parse as hex code
        match s with
          | u::h1::h2::h3::h4::tail' -> 
              let h1_parse = parse_json_hex [h1] in
              let h2_parse = parse_json_hex [h2] in
              let h3_parse = parse_json_hex [h3] in
              let h4_parse = parse_json_hex [h4] in
              if (G.char_from_codepoint 0x75 = u) && (Some? h1_parse) && (Some? h2_parse) && (Some? h3_parse) && (Some? h4_parse) then
                Some {
                  result = G.HexCode u (Some?.v h1_parse).result (Some?.v h2_parse).result (Some?.v h3_parse).result (Some?.v h4_parse).result;
                  remainder = tail'
                }
              else
                None
          | _ -> None

let parse_json_escape_soundness (s: string) :
  Lemma
  (requires (Some? (parse_json_escape (String.list_of_string s))))
  (ensures (parser_soundness parse_json_escape G.render_json_escape s)) 
  =
  let c::tail = String.list_of_string s in
  // Handle the escape char
  let is_escape_char = G.char_from_codepoint 0x22 = c || // '"'
                      G.char_from_codepoint 0x5C = c || // '\'
                      G.char_from_codepoint 0x2F = c || // '/'
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
        let hex_parse_helper (h: char{Some? (parse_json_hex [h])}) : Lemma (ensures (G.char_to_str h) == (G.render_json_hex (Some?.v (parse_json_hex [h])).result)) =
          (
            String.list_of_string_of_list [h];
            parse_json_hex_soundness (G.char_to_str h);
            postpend_empty_is_identity (G.char_to_str h);
            String.list_of_string_of_list [h];
            str_decompose (G.char_to_str h) [h] []
          )
        in
        // Substitute hi' for i=1,2,3,4 in the decomposition to get soundness theorem
        hex_parse_helper h1;
        hex_parse_helper h2;
        hex_parse_helper h3;
        hex_parse_helper h4
      )
      | _ -> ()

let parse_json_escape_completeness (escape: G.json_escape) :
  Lemma
  (ensures (parser_completeness parse_json_escape G.render_json_escape escape))
  =
  let rendered_escape = G.render_json_escape escape in
  match escape with
    | G.Escape c -> (
      String.list_of_string_of_list [c];
      str_decompose rendered_escape [c] [];
      assert((Some?.v (parse_json_escape (String.list_of_string rendered_escape))).result == escape);
      let c::tail = String.list_of_string rendered_escape in
      string_of_list_eq tail [];
      ()
    )
    | G.HexCode u h0 h1 h2 h3 -> (
      let u' = String.string_of_list [u] in
      // Helper lemma to prove that hex digits render into one character
      hex_is_char h0;
      hex_is_char h1;
      hex_is_char h2;
      hex_is_char h3;
      let h0_s = G.render_json_hex h0 in
      let h1_s = G.render_json_hex h1 in
      let h2_s = G.render_json_hex h2 in
      let h3_s = G.render_json_hex h3 in
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
      assert((G.char_to_str h0') == G.render_json_hex h0);
      assert((G.char_to_str h1') == G.render_json_hex h1);
      assert((G.char_to_str h2') == G.render_json_hex h2);
      assert((G.char_to_str h3') == G.render_json_hex h3);
      // We now proved that input to hex parser effectively from a hex production rule allowing us to use completeness
      parse_json_hex_completeness h0;
      parse_json_hex_completeness h1;
      parse_json_hex_completeness h2;
      parse_json_hex_completeness h3
    )

let rec parse_json_digits (s: list char) : Tot (option (parser_result G.json_digits)) =
  match parse_json_digit s with
    | Some { result=digit; remainder=remainder } -> (
      // Prove termination of recursive call by proving successfully digit parse yields a strictly smaller remainder
      String.list_of_string_of_list s;
      parse_json_digit_soundness (String.string_of_list s); // Soundness provides a useable decomposition to reason about the length of remainder
      assert (String.string_of_list s == G.render_json_digit digit ^ String.string_of_list remainder);
      String.concat_length (G.render_json_digit digit) (String.string_of_list remainder);
      digit_len_one digit;
      match parse_json_digits remainder with
        | Some res -> Some {
          result = G.Digits digit res.result;
          remainder = res.remainder
        }
        | None -> Some {
          result = G.DigitsSingle digit;
          remainder = remainder
        }
    )
    | None -> None

let rec parse_json_digits_soundness (s: string) :
  Lemma
  (requires Some? (parse_json_digits (String.list_of_string s)))
  (ensures parser_soundness parse_json_digits G.render_json_digits s)
  (decreases String.strlen s)
  =
  match parse_json_digit (String.list_of_string s) with
    | Some { result=digit; remainder=remainder } -> (
      parse_json_digit_soundness s;
      // By digit soundness, s = render_json_digit digit + remainder
      match parse_json_digits remainder with
        | Some res -> (
          // Use same proof in parser to prove termination
          String.concat_length (G.render_json_digit digit) (String.string_of_list remainder);
          digit_len_one digit;
          String.list_of_string_of_list remainder;
          parse_json_digits_soundness (String.string_of_list remainder);
          str_concat_assoc (G.render_json_digit digit) (G.render_json_digits res.result) (String.string_of_list res.remainder)
        )
        | None -> ()
    )

let rec parse_json_digits_completeness (digits: G.json_digits) :
  Lemma
  (ensures (parser_completeness parse_json_digits G.render_json_digits digits))
  =
  match digits with
    | G.DigitsSingle digit -> (
      // This case reduces to using completeness of digit parser
      parse_json_digit_completeness digit;
      match parse_json_digit (String.list_of_string (G.render_json_digits digits)) with
        | Some {result=digit; remainder=remainder} -> (
          assert(remainder == []);
          assert(None? (parse_json_digit remainder));
          assert(None? (parse_json_digits remainder))
        )
    )
    | G.Digits digit digits' -> (
      let rendered_digits = G.render_json_digits digits in
      let digit_list = String.list_of_string (G.render_json_digit digit) in
      let digits'_list = String.list_of_string (G.render_json_digits digits') in
      // rendered_digits = (render_json_digit digit) + (render_json_digits digits')
      String.list_of_concat (G.render_json_digit digit) (G.render_json_digits digits');
      // Break of rendered digits into a list for easier analysis on the digit parsing
      assert(String.list_of_string rendered_digits == digit_list @ digits'_list);
      // Case analysis on digit to show that soundness assumption holds
      (
        match digit with
          | G.DigitZero c -> (
            // Give hint to FStar to prove that c comes from digit_list
            String.list_of_string_of_list [c];
            assert(Some? (parse_json_digit (String.list_of_string rendered_digits)))
          )
          | G.DigitOneNine (G.OneNine c) -> (
            // Give hint to FStar to prove that c comes from digit_list
            String.list_of_string_of_list [c];
            assert(Some? (parse_json_digit (String.list_of_string rendered_digits)))
          )
      );
      // Use soundness to decompose rendered digits to show that the remainder was generated by digits'
      // where we can then reapply completeness
      parse_json_digit_soundness rendered_digits;
      let Some { result=digit; remainder=remainder } = parse_json_digit (String.list_of_string rendered_digits) in
      // Show that our two decompositions (digit_list w/ digits'_list and digit w/ remainder) are equivalent
      String.concat_injective 
        (G.render_json_digit digit)
        (G.render_json_digit digit)
        (String.string_of_list remainder)
        (G.render_json_digits digits');
      assert(String.string_of_list remainder == G.render_json_digits digits');
      parse_json_digits_completeness digits'
    )

let parse_json_fraction (s: list char) : parser_result G.json_fraction =
  match s with
    | [] -> { result=G.NoFraction; remainder = s }
    | c::tail -> 
      if G.char_from_codepoint 0x2E = c then // '.'
        match parse_json_digits tail with
          | Some parsed_digits -> { result = G.Fraction c parsed_digits.result; remainder = parsed_digits.remainder}
          | None -> { result=G.NoFraction; remainder = s }
      else
        { result=G.NoFraction; remainder = s }

let parse_json_fraction_soundness (s: string) :
  Lemma
  (ensures (parser_soundness (infallible_to_fallible_parser parse_json_fraction) G.render_json_fraction s))
  =
  String.string_of_list_of_string s;
  match String.list_of_string s with
    | [] -> prepend_empty_is_identity s
    | c::tail -> 
      if G.char_from_codepoint 0x2E = c then // '.'
      (
        str_decompose s [c] tail;
        match parse_json_digits tail with
          | Some parsed_digits -> (
            String.list_of_string_of_list tail;
            parse_json_digits_soundness (String.string_of_list tail);
            str_concat_assoc (String.string_of_list [c]) (G.render_json_digits parsed_digits.result) (String.string_of_list parsed_digits.remainder)
          )
          | None -> prepend_empty_is_identity s
      )
      else
        prepend_empty_is_identity s

let parse_json_fraction_completeness (fraction: G.json_fraction) :
  Lemma
  (ensures (parser_completeness (infallible_to_fallible_parser parse_json_fraction) G.render_json_fraction fraction))
  =
  let rendered_fraction = G.render_json_fraction fraction in
  match fraction with
    | G.NoFraction -> list_of_string_eq rendered_fraction ""
    | G.Fraction c digits -> (
      // rendered_fraction = (G.char_to_str c) + (rendered_json_digits digits)
      String.list_of_concat (G.char_to_str c) (G.render_json_digits digits);
      String.list_of_string_of_list [c];
      let c::tail = String.list_of_string rendered_fraction in
      str_decompose rendered_fraction [c] tail;
      String.concat_injective (G.char_to_str c) (G.char_to_str c) (G.render_json_digits digits) (String.string_of_list tail);
      assert (G.render_json_digits digits == String.string_of_list tail);
      parse_json_digits_completeness digits
    )

let parse_json_exponent (s: list char) : parser_result G.json_exponent =
  match s with
    | [] -> { result=G.NoExponent; remainder=s }
    | c::tail -> 
      if (G.char_from_codepoint 0x65 = c) || (G.char_from_codepoint 0x45 = c) then
        let parsed_json_sign = parse_json_sign tail in
        match parse_json_digits (parsed_json_sign.remainder) with
          | Some parsed_digits -> {
            result = G.Exponent c parsed_json_sign.result parsed_digits.result;
            remainder = parsed_digits.remainder
          }
          | None -> { result=G.NoExponent; remainder=s }
      else
        { result=G.NoExponent; remainder=s }

let parse_json_exponent_soundness (s: string) :
  Lemma
  (ensures parser_soundness (infallible_to_fallible_parser parse_json_exponent) G.render_json_exponent s)
  =
  String.string_of_list_of_string s;
  match String.list_of_string s with
    | [] -> prepend_empty_is_identity s
    | c::tail -> 
      str_decompose s [c] tail;
      if (G.char_from_codepoint 0x65 = c) || (G.char_from_codepoint 0x45 = c) then
        let parsed_json_sign = parse_json_sign tail in
        String.list_of_string_of_list tail;
        parse_json_sign_soundness (String.string_of_list tail);
        match parse_json_digits (parsed_json_sign.remainder) with
          | Some parsed_digits -> (
            String.list_of_string_of_list parsed_json_sign.remainder;
            parse_json_digits_soundness (String.string_of_list parsed_json_sign.remainder);
            assert(s == (G.char_to_str c) ^ ((G.render_json_sign parsed_json_sign.result) ^ ((G.render_json_digits parsed_digits.result) ^ (String.string_of_list parsed_digits.remainder))));
            str_concat_assoc (G.render_json_sign parsed_json_sign.result) (G.render_json_digits parsed_digits.result) (String.string_of_list parsed_digits.remainder);
            str_concat_assoc (G.char_to_str c) ((G.render_json_sign parsed_json_sign.result) ^ (G.render_json_digits parsed_digits.result)) (String.string_of_list parsed_digits.remainder)
          )
          | None -> prepend_empty_is_identity s
      else
        prepend_empty_is_identity s

let parse_json_exponent_completeness (exponent: G.json_exponent) :
  Lemma
  (ensures parser_completeness (infallible_to_fallible_parser parse_json_exponent) G.render_json_exponent exponent)
  =
  let rendered_exponent = G.render_json_exponent exponent in
  match exponent with
    | G.NoExponent -> list_of_string_eq rendered_exponent ""
    | G.Exponent c sign digits ->
      let rendered_sign = G.render_json_sign sign in
      let rendered_digits = G.render_json_digits digits in
      // rendered_exponent = (G.char_to_str c) + rendered_sign + rendered_digits
      String.list_of_concat (G.char_to_str c) (rendered_sign ^ rendered_digits);
      String.list_of_concat rendered_sign rendered_digits;
      String.list_of_string_of_list [c];
      let c::tail = String.list_of_string rendered_exponent in
      str_decompose rendered_exponent [c] tail;
      // string_of_list tail = rendered_sign + rendered_digits
      String.concat_injective (G.char_to_str c) (G.char_to_str c) (String.string_of_list tail) (rendered_sign ^ rendered_digits);
      String.list_of_string_of_list tail;
      match sign with
        | G.NoSign -> (
          // rendered_sign = ""
          prepend_empty_is_identity rendered_digits;
          assert(String.string_of_list tail == rendered_digits);
          // Prove that rendered_digits start with a character '0' to '9' making the sign parser yield NoSign
          digits_start_character digits;
          assert((parse_json_sign (String.list_of_string rendered_digits)).result == G.NoSign);
          assert(String.string_of_list (parse_json_sign (String.list_of_string rendered_digits)).remainder == rendered_digits);
          parse_json_digits_completeness digits
        )
        | G.PlusMinus pm -> (
          String.list_of_string_of_list [pm];
          str_decompose (String.string_of_list tail) [pm] (String.list_of_string rendered_digits);
          let pm::tail' = tail in
          parse_json_sign_soundness (String.string_of_list tail);
          assert((parse_json_sign tail).result == G.PlusMinus pm);
          assert((parse_json_sign tail).remainder == tail');
          String.concat_injective 
            (G.char_to_str pm)
            (G.char_to_str pm)
            (String.string_of_list (parse_json_sign tail).remainder)
            rendered_digits;
          parse_json_digits_completeness digits
        )

let parse_json_integer (s: list char) : option (parser_result G.json_integer) =
  match s with
    | [] -> None
    | c::tail -> if G.char_from_codepoint 0x2D = c then
      // Negative branch
      match parse_json_digit tail with
        | Some ({ result=G.DigitZero d; remainder=remainder }) -> Some { result=G.IntNegDigit c (G.DigitZero d); remainder=remainder }
        | Some ({ result=G.DigitOneNine (G.OneNine d); remainder=remainder }) -> (
            match parse_json_digits remainder with
              | Some { result=digits; remainder=remainder } -> Some { result=G.IntNegDigits c (G.OneNine d) digits; remainder=remainder }
              | None -> Some { result=G.IntNegDigit c (G.DigitOneNine (G.OneNine d)); remainder=remainder }
        )
        | None -> None
    else
      // Non-negative branch
      match parse_json_digit s with
        | Some ({ result=G.DigitZero d; remainder=remainder }) -> Some { result=G.IntDigit (G.DigitZero d); remainder=remainder }
        | Some ({ result=G.DigitOneNine (G.OneNine d); remainder=remainder }) -> (
            match parse_json_digits remainder with
              | Some { result=digits; remainder=remainder } -> Some { result=G.IntDigits (G.OneNine d) digits; remainder=remainder }
              | None -> Some { result=G.IntDigit (G.DigitOneNine (G.OneNine d)); remainder=remainder }
        )
        | None -> None

let parse_json_integer_soundness (s: string) :
  Lemma
  (requires (Some? (parse_json_integer (String.list_of_string s))))
  (ensures (parser_soundness parse_json_integer G.render_json_integer s))
  =
  String.string_of_list_of_string s;
  let c::tail = String.list_of_string s in
  if G.char_from_codepoint 0x2D = c then
  (
    str_decompose s [c] tail;
    String.list_of_string_of_list tail;
    parse_json_digit_soundness (String.string_of_list tail);
    match parse_json_digit tail with
      | Some ({ result=G.DigitZero d; remainder=remainder }) -> str_concat_assoc (G.char_to_str c) (G.char_to_str d) (String.string_of_list remainder)
      | Some ({ result=G.DigitOneNine (G.OneNine d); remainder=remainder }) -> (
        match parse_json_digits remainder with
          | Some { result=digits; remainder=remainder' } -> (
            String.list_of_string_of_list remainder;
            parse_json_digits_soundness (String.string_of_list remainder);
            str_concat_assoc (G.char_to_str d) (G.render_json_digits digits) (String.string_of_list remainder');
            str_concat_assoc (G.char_to_str c) (G.char_to_str d ^ G.render_json_digits digits) (String.string_of_list remainder')
          )
          | None -> str_concat_assoc (G.char_to_str c) (G.char_to_str d) (String.string_of_list remainder)
      )
  )
  else
    parse_json_digit_soundness s;
    match parse_json_digit (String.list_of_string s) with
      | Some ({ result=G.DigitZero d; remainder=remainder }) -> ()
      | Some ({ result=G.DigitOneNine (G.OneNine d); remainder=remainder }) -> (
          match parse_json_digits remainder with
            | Some { result=digits; remainder=remainder' } -> (
              String.list_of_string_of_list remainder;
              parse_json_digits_soundness (String.string_of_list remainder);
              str_concat_assoc (G.char_to_str d) (G.render_json_digits digits) (String.string_of_list remainder')
            )
            | None -> ()
      )
      | None -> ()

let parse_json_integer_completeness (integer: G.json_integer) :
  Lemma
  (ensures parser_completeness parse_json_integer G.render_json_integer integer)
  =
  let rendered_integer = G.render_json_integer integer in
  match integer with
    | G.IntDigit (G.DigitZero c) -> (
      parse_json_digit_completeness (G.DigitZero c)
    )
    | G.IntDigit (G.DigitOneNine (G.OneNine c)) -> (
      parse_json_digit_completeness (G.DigitOneNine (G.OneNine c))
    )
    | G.IntDigits (G.OneNine c) digits -> (
      String.list_of_concat (G.render_json_onenine (G.OneNine c)) (G.render_json_digits digits);
      String.list_of_string_of_list [c];
      let c::tail = String.list_of_string rendered_integer in
      let Some {result=G.DigitOneNine (G.OneNine c); remainder=remainder} = parse_json_digit (String.list_of_string rendered_integer) in
      parse_json_digit_soundness rendered_integer;
      // Use the two decompositions of rendered_integers and prove equivalence
      String.concat_injective (G.char_to_str c) (G.char_to_str c) (String.string_of_list remainder) (G.render_json_digits digits);
      parse_json_digits_completeness digits
    )
    | G.IntNegDigit minus (G.DigitZero c) -> (
      String.list_of_concat (G.char_to_str minus) (G.char_to_str c);
      String.list_of_string_of_list [minus];
      String.list_of_string_of_list [c];
      parse_json_digit_completeness (G.DigitZero c)
    )
    | G.IntNegDigit minus (G.DigitOneNine (G.OneNine c)) -> (
      String.list_of_concat (G.char_to_str minus) (G.char_to_str c);
      String.list_of_string_of_list [minus];
      String.list_of_string_of_list [c];
      parse_json_digit_completeness (G.DigitOneNine (G.OneNine c))
    )
    | G.IntNegDigits minus (G.OneNine c) digits -> (
      String.list_of_concat (G.char_to_str minus) ((G.render_json_onenine (G.OneNine c)) ^ (G.render_json_digits digits));
      String.list_of_string_of_list [minus];
      String.list_of_string_of_list [c];
      let c'::tail = String.list_of_string rendered_integer in
      str_decompose rendered_integer [c'] tail;
      // Decompose and get back to the usual IntDigits case and replay that proof
      String.concat_injective (G.char_to_str minus) (G.char_to_str minus) (String.string_of_list tail) ((G.render_json_onenine (G.OneNine c)) ^ (G.render_json_digits digits));
      String.list_of_concat (G.render_json_onenine (G.OneNine c)) (G.render_json_digits digits);
      let c::tail' = tail  in
      let Some {result=G.DigitOneNine (G.OneNine c); remainder=remainder} = parse_json_digit tail in
      parse_json_digit_soundness (String.string_of_list tail);
      String.concat_injective (G.char_to_str c) (G.char_to_str c) (String.string_of_list remainder) (G.render_json_digits digits);
      parse_json_digits_completeness digits
    )

let parse_json_number (s: list char) : option (parser_result G.json_number) = 
  match parse_json_integer s with
    | Some { result=integer; remainder=remainder } -> (
      let { result=fraction; remainder=remainder } = parse_json_fraction remainder in
      let { result=exponent; remainder=remainder } = parse_json_exponent remainder in
      Some {
        result = G.Number integer fraction exponent;
        remainder = remainder
      }
    )
    | None -> None

let parse_json_number_soundness (s: string) :
  Lemma
  (requires (Some? (parse_json_number (String.list_of_string s))))
  (ensures (parser_soundness parse_json_number G.render_json_number s))
  =
  parse_json_integer_soundness s;
  let Some { result=integer; remainder=remainder } = parse_json_integer (String.list_of_string s) in
  String.list_of_string_of_list remainder;
  parse_json_fraction_soundness (String.string_of_list remainder);
  let { result=fraction; remainder=remainder' } = parse_json_fraction remainder in
  String.list_of_string_of_list remainder';
  parse_json_exponent_soundness (String.string_of_list remainder');
  let { result=exponent; remainder=remainder'' } = parse_json_exponent remainder' in
  str_concat_assoc (G.render_json_fraction fraction) (G.render_json_exponent exponent) (String.string_of_list remainder'');
  str_concat_assoc (G.render_json_integer integer) ((G.render_json_fraction fraction) ^ (G.render_json_exponent exponent)) (String.string_of_list remainder'')

// Let s1 and s2 be two strings such that s2 does not begin with a digit character.
// This lemma asserts that parsing s1 with "parse_json_digits" will yield the same
// result of parsing s1^s2, ignoring the remainder. By soundness, this implies 
// parsing s1 and s1^s2 "terminate at the same place".
let rec parse_json_digits_termination (s1 s2: string) :
  Lemma
  (requires that_first_char_of s2 (fun c -> not (is_digit_char c)))
  (ensures matching_parse_result s1 (s1 ^ s2) parse_json_digits)
  (decreases String.strlen s1)
  =
  match String.list_of_string s1 with
    | [] -> (
      assert(None? (parse_json_digits (String.list_of_string s1)));
      string_of_list_eq [] (String.list_of_string s1);
      String.string_of_list_of_string s1;
      assert(s1 == "");
      prepend_empty_is_identity s2
      // By assumption of s2 not starting with digit char by case analysis of s2 we are done
    )
    | c::tail -> (
      // Perform the following decomposition: 
      //    s1 = c + tail
      str_decompose s1 [c] tail;
      String.list_of_string_of_list [c];
      String.list_of_string_of_list tail;
      //    s1+s2 = c + (tail + s2)
      str_concat_assoc (G.char_to_str c) (String.string_of_list tail) s2;
      String.list_of_concat (G.char_to_str c) ((String.string_of_list tail) ^ s2);
      String.string_of_list_of_string ((String.string_of_list tail) ^ s2);

      // Then use induction to prove that parsing tail and tail+s2 gives the same result
      if is_digit_char c then (
        let Some { result=digit_original; remainder=remainder_original } = parse_json_digit (String.list_of_string s1) in
        let Some { result=digit_concat; remainder=remainder_concat } = parse_json_digit (String.list_of_string (s1^s2)) in
        assert(digit_original == digit_concat);
        assert(remainder_original == tail);
        assert(String.string_of_list remainder_concat == ((String.string_of_list tail) ^ s2));
        // We now have the pieces in place to invoke the induction hypothesis to complete the proof
        str_tail_decrease s1; // used to prove recursive termination
        parse_json_digits_termination (String.string_of_list tail) s2
      )
      else (
        assert(None? (parse_json_digits (String.list_of_string s1)));
        assert(None? (parse_json_digits (String.list_of_string (s1^s2))))
      )
    )

// Similar to parse_json_digits_termination
let parse_json_integer_termination (s1 s2: string) :
  Lemma
  (requires that_first_char_of s2 (fun c -> not (is_digit_char c) && not (c = G.char_from_codepoint 0x2D))) // First character of s2cannot be digit or negative sign
  (ensures matching_parse_result s1 (s1 ^ s2) parse_json_integer)
  =
  match String.list_of_string s1 with
    | [] -> (
      assert(None? (parse_json_digits (String.list_of_string s1)));
      string_of_list_eq [] (String.list_of_string s1);
      String.string_of_list_of_string s1;
      assert(s1 == "");
      prepend_empty_is_identity s2
    )
    | c::tail -> (
      // Perform the following decomposition: 
      //    s1 = c + tail
      str_decompose s1 [c] tail;
      String.list_of_string_of_list [c];
      //    s1+s2 = c + (tail + s2)
      str_concat_assoc (G.char_to_str c) (String.string_of_list tail) s2;
      String.list_of_concat (G.char_to_str c) ((String.string_of_list tail) ^ s2);
      String.string_of_list_of_string ((String.string_of_list tail) ^ s2);
      // Decompose tail+s2 to assist FStar in analyzing the "tail" of the concatenated string
      String.list_of_concat (String.string_of_list tail) s2;
      String.list_of_string_of_list tail;

      if G.char_from_codepoint 0x2D = c then
      (
        match parse_json_digit tail with
          | Some ({ result=G.DigitZero d; remainder=remainder }) -> ()
          | Some ({ result=G.DigitOneNine (G.OneNine d); remainder=remainder }) -> (
              // s = c + tail = c + d + remainder
              // s1+s2 = c + d + remainder + s2
              // Inspect proof state
              let Some ({ result=G.DigitOneNine (G.OneNine d_concat); remainder=remainder_concat }) = parse_json_digit (String.list_of_string ((String.string_of_list tail)^s2)) in
              assert(d == d_concat);
              parse_json_digit_soundness (String.string_of_list tail);
              parse_json_digit_soundness ((String.string_of_list tail) ^ s2);
              str_concat_assoc (G.char_to_str d) (String.string_of_list remainder) s2;
              String.concat_injective 
                (G.char_to_str d)
                (G.char_to_str d_concat)
                ((String.string_of_list remainder)^s2)
                (String.string_of_list remainder_concat);
              assert((String.string_of_list remainder)^s2 == String.string_of_list remainder_concat);

              // Finally! We can use the termination property of parse_json_digits
              parse_json_digits_termination (String.string_of_list remainder) s2;
              String.list_of_string_of_list remainder;
              String.list_of_concat (String.string_of_list remainder) s2
          )
          | None -> ()
      )
      else
      (
        parse_json_digits_termination s1 s2
      )
    )

// Similar to parse_json_digits_termination
let parse_json_fraction_termination (s1 s2: string) :
  Lemma
  (requires that_first_char_of s2 (fun c -> not (is_digit_char c) && not (c = G.char_from_codepoint 0x2E))) // First character of s2 cannot be digit or period
  (ensures matching_parse_result s1 (s1 ^ s2) (infallible_to_fallible_parser parse_json_fraction))
  =
  String.list_of_concat s1 s2;
  match String.list_of_string s1 with 
    | [] -> (
      assert(None? (parse_json_digits (String.list_of_string s1)));
      string_of_list_eq [] (String.list_of_string s1);
      String.string_of_list_of_string s1;
      assert(s1 == "");
      prepend_empty_is_identity s2
    )
    | c::tail -> (
      // Perform the following decomposition: 
      //    s1 = c + tail
      str_decompose s1 [c] tail;
      String.list_of_string_of_list [c];
      //    s1+s2 = c + (tail + s2)
      str_concat_assoc (G.char_to_str c) (String.string_of_list tail) s2;
      String.list_of_concat (G.char_to_str c) ((String.string_of_list tail) ^ s2);
      String.string_of_list_of_string ((String.string_of_list tail) ^ s2);
      parse_json_digits_termination (String.string_of_list tail) s2;
      String.list_of_concat (String.string_of_list tail) s2;
      String.list_of_string_of_list tail
    )

// Similar to parse_json_digits_termination
let parse_json_exponent_termination (s1 s2: string) :
  Lemma
  (requires that_first_char_of s2 (
    // First character of s2 cannot be digit or 'e'/'E' or '+'/'-'
    fun c -> 
      not (is_digit_char c) && 
      not (c = G.char_from_codepoint 0x65) && 
      not (c = G.char_from_codepoint 0x45) &&
      not (c = G.char_from_codepoint 0x2B) &&
      not (c = G.char_from_codepoint 0x2D)
  ))
  (ensures matching_parse_result s1 (s1 ^ s2) (infallible_to_fallible_parser parse_json_exponent))
  =
  String.list_of_concat s1 s2;
  match String.list_of_string s1 with 
    | [] -> (
      assert(None? (parse_json_digits (String.list_of_string s1)));
      string_of_list_eq [] (String.list_of_string s1);
      String.string_of_list_of_string s1;
      assert(s1 == "");
      prepend_empty_is_identity s2
    )
    | c::tail -> (
      // Perform the following decomposition: 
      //    s1 = c + tail
      str_decompose s1 [c] tail;
      String.list_of_string_of_list [c];
      //    s1+s2 = c + (tail + s2)
      str_concat_assoc (G.char_to_str c) (String.string_of_list tail) s2;
      String.list_of_concat (G.char_to_str c) ((String.string_of_list tail) ^ s2);
      String.string_of_list_of_string ((String.string_of_list tail) ^ s2);

      if (G.char_from_codepoint 0x65 = c) || (G.char_from_codepoint 0x45 = c) then
        let {result=sign1; remainder=remainder1} = parse_json_sign tail in
        let {result=sign2; remainder=remainder2} = parse_json_sign (String.list_of_string ((String.string_of_list tail) ^ s2)) in
        (
        String.list_of_string_of_list tail;
        match tail with
          | [] -> (
            string_of_list_eq tail [];
            prepend_empty_is_identity s2;
            assert(sign1 == sign2)
          )
          | c'::tail' ->
            // Decompose tail + s2 = c' + tail' + s2 to prove that tail + s2 starts with c'
            // leading to same sign parsing
            str_decompose (String.string_of_list tail) [c'] tail';
            str_concat_assoc (G.char_to_str c') (String.string_of_list tail') s2;
            String.list_of_string_of_list [c'];
            String.list_of_concat (G.char_to_str c') ((String.string_of_list tail') ^ s2);
            assert(sign1 == sign2)
        );
        assert(sign1 == sign2);
        // sign1 + remainder1 + s2 = tail + s2 = sign2 + remainder
        parse_json_sign_soundness (String.string_of_list tail);
        parse_json_sign_soundness ((String.string_of_list tail) ^ s2);
        String.concat_injective 
          (G.render_json_sign sign1)
          (G.render_json_sign sign2)
          ((String.string_of_list remainder1) ^ s2)
          (String.string_of_list remainder2);
        assert (String.string_of_list remainder2 == (String.string_of_list remainder1) ^ s2);
        parse_json_digits_termination (String.string_of_list remainder1) s2;
        String.list_of_concat (String.string_of_list remainder1) s2;
        String.list_of_string_of_list remainder1
      else
        ()
    )

let parse_json_number_completeness (number: G.json_number) :
  Lemma
  (ensures parser_completeness parse_json_number G.render_json_number number)
  =
  let rendered_number = G.render_json_number number in
  let G.Number integer fraction exponent = number in
  let rendered_integer = G.render_json_integer integer in
  let rendered_fraction = G.render_json_fraction fraction in
  let rendered_exponent = G.render_json_exponent exponent in
  json_fraction_empty_or_period fraction;
  json_exponent_empty_or_e exponent;
  // rendered_number = rendered_integer + (rendered_fraction + rendered_exponent)
  str_concat_assoc rendered_integer rendered_fraction rendered_exponent;

  // Handle phase 1 of parsing the integer part
  parse_json_integer_termination (rendered_integer ^ rendered_fraction) rendered_exponent;
  parse_json_integer_termination rendered_integer rendered_fraction;
  parse_json_integer_completeness integer;
  parse_json_integer_soundness rendered_number;
  let Some {result=integer'; remainder=remainder} = parse_json_integer (String.list_of_string rendered_number) in
  assert(integer == integer');
  String.concat_length rendered_integer (rendered_fraction ^ rendered_exponent);
  String.concat_length (G.render_json_integer integer') (String.string_of_list remainder);
  assert(String.strlen rendered_integer == String.strlen (G.render_json_integer integer'));
  assert(String.strlen (rendered_fraction ^ rendered_exponent) == String.strlen (String.string_of_list remainder));
  String.concat_injective 
    rendered_integer
    (G.render_json_integer integer')
    (rendered_fraction ^ rendered_exponent)
    (String.string_of_list remainder);
  assert(String.string_of_list remainder == rendered_fraction ^ rendered_exponent);

  // Handle phase 2 of parsing the fraction part
  parse_json_fraction_termination rendered_fraction rendered_exponent;
  parse_json_fraction_completeness fraction;
  parse_json_fraction_soundness (String.string_of_list remainder);
  String.list_of_string_of_list remainder;
  let {result=fraction'; remainder=remainder} = parse_json_fraction remainder in
  assert(fraction == fraction');
  String.concat_length rendered_fraction rendered_exponent;
  String.concat_length (G.render_json_fraction fraction') (String.string_of_list remainder);
  String.concat_injective
    rendered_fraction
    (G.render_json_fraction fraction')
    rendered_exponent
    (String.string_of_list remainder);
  assert(String.string_of_list(remainder) == rendered_exponent);

  // Handle phase 3 of parsing the exponent part
  String.list_of_string_of_list remainder;
  parse_json_exponent_completeness exponent

let parse_json_number_termination (number: G.json_number) (s: string):
  Lemma
  (requires (that_first_char_of s (fun c -> is_char_not_json_number_extendable c)))
  (ensures (matching_parse_result (G.render_json_number number) ((G.render_json_number number) ^ s) parse_json_number))
  =
  let rendered_number = G.render_json_number number in
  let G.Number integer fraction exponent = number in
  let rendered_integer = G.render_json_integer integer in
  let rendered_fraction = G.render_json_fraction fraction in
  let rendered_exponent = G.render_json_exponent exponent in
  json_fraction_empty_or_period fraction;
  json_exponent_empty_or_e exponent;

  // Handle rendered_number case
  // rendered_number = rendered_integer + (rendered_fraction + rendered_exponent)
  str_concat_assoc rendered_integer rendered_fraction rendered_exponent;
  parse_json_integer_termination (rendered_integer ^ rendered_fraction) rendered_exponent;
  String.list_of_concat (rendered_integer ^ rendered_fraction) rendered_exponent;
  parse_json_integer_termination rendered_integer rendered_fraction;
  String.list_of_concat rendered_integer rendered_fraction;
  parse_json_integer_completeness integer;
  parse_json_integer_soundness rendered_number;
  let Some {result=integer'; remainder=remainder} = parse_json_integer (String.list_of_string rendered_number) in
  String.list_of_string_of_list remainder;
  String.concat_length rendered_integer (rendered_fraction ^ rendered_exponent);
  String.concat_length (G.render_json_integer integer') (String.string_of_list remainder);
  String.concat_injective 
    rendered_integer
    (G.render_json_integer integer')
    (rendered_fraction ^ rendered_exponent)
    (String.string_of_list remainder);
  parse_json_fraction_termination rendered_fraction rendered_exponent;
  String.list_of_concat rendered_fraction rendered_exponent;
  parse_json_fraction_completeness fraction;
  parse_json_fraction_soundness (String.string_of_list remainder);
  let {result=fraction'; remainder=remainder} = parse_json_fraction remainder in
  String.list_of_string_of_list remainder;
  String.concat_length rendered_fraction rendered_exponent;
  String.concat_length (G.render_json_fraction fraction') (String.string_of_list remainder);
  String.concat_injective 
    rendered_fraction
    (G.render_json_fraction fraction')
    rendered_exponent
    (String.string_of_list remainder);

  // Handle rendered_number ^ s case
  // rendered_number + s = (rendered_integer + rendered_fraction + rendered_exponent) + s
  String.list_of_concat rendered_number s;
  str_concat_assoc rendered_integer rendered_fraction rendered_exponent;
  str_concat_assoc rendered_integer (rendered_fraction ^ rendered_exponent) s;
  str_concat_assoc rendered_fraction rendered_exponent s;

  parse_json_integer_termination (rendered_integer ^ rendered_fraction ^ rendered_exponent) s;
  String.list_of_concat (rendered_integer ^ rendered_fraction ^ rendered_exponent) s;
  parse_json_integer_soundness (rendered_number ^ s);
  let Some {result=integer'; remainder=remainder} = parse_json_integer (String.list_of_string (rendered_number ^ s)) in
  String.list_of_string_of_list remainder;
  String.concat_length rendered_integer (rendered_fraction ^ rendered_exponent ^ s);
  String.concat_length (G.render_json_integer integer') (String.string_of_list remainder);
  String.concat_injective rendered_integer 
    (G.render_json_integer integer')
    (rendered_fraction ^ rendered_exponent ^ s) 
    (String.string_of_list remainder);
  // Justify precondition of fraction termination for rendered_exponent ^ s
  prepend_empty_is_identity s; // NoExponent case
  String.list_of_concat rendered_exponent s; // Exponent case
  parse_json_fraction_termination rendered_fraction (rendered_exponent ^ s);
  String.list_of_concat rendered_fraction (rendered_exponent ^ s);
  parse_json_fraction_completeness fraction;
  parse_json_fraction_soundness (String.string_of_list remainder);
  let {result=fraction'; remainder=remainder} = parse_json_fraction remainder in
  String.list_of_string_of_list remainder;
  String.concat_length rendered_fraction (rendered_exponent ^ s);
  String.concat_length (G.render_json_fraction fraction') (String.string_of_list remainder);
  String.concat_injective 
    rendered_fraction 
    (G.render_json_fraction fraction') 
    (rendered_exponent ^ s) 
    (String.string_of_list remainder);

  // Invoke exponent termination to prove the final step that the parse_json_exponent stage is the same
  parse_json_exponent_termination (G.render_json_exponent exponent) s

let parse_json_character (s: list char) : option (parser_result G.json_character) =
  match s with
    | [] -> None
    | c::tail -> 
      let codepoint = U32.v (Char.u32_of_char c) in
      let unescaped_char = 
        not (G.char_from_codepoint 0x22 = c) &&          // '"'
        not (G.char_from_codepoint 0x5C = c) &&          // '\'
        not (0x00 <= codepoint && codepoint <= 0x1F)   // Control characters
      in
      if unescaped_char then
        Some { result = G.Character c; remainder = tail }
      else if G.char_from_codepoint 0x5C = c then // '\'
        match parse_json_escape tail with
          | None -> None
          | Some { result = escape_result; remainder = escape_remainder } -> Some { result = G.EscapedCharacter c escape_result; remainder = escape_remainder }
      else
         None

let parse_json_character_soundness (s: string) :
  Lemma
  (requires (Some? (parse_json_character (String.list_of_string s))))
  (ensures (parser_soundness parse_json_character G.render_json_character s))
  =
  match String.list_of_string s with
    | c::tail -> 
      let codepoint = U32.v (Char.u32_of_char c) in
      let unescaped_char = 
        not (G.char_from_codepoint 0x22 = c) &&          // '"'
        not (G.char_from_codepoint 0x5C = c) &&          // '\'
        not (0x00 <= codepoint && codepoint <= 0x1F)   // Control characters
      in
      str_decompose s [c] tail;
      if unescaped_char then
        String.list_of_concat (G.char_to_str c) (String.string_of_list tail)
      else if G.char_from_codepoint 0x5C = c then // '\'
        match parse_json_escape tail with
          | Some { result = escape_result; remainder = escape_remainder } -> (
            String.list_of_string_of_list tail;
            parse_json_escape_soundness (String.string_of_list tail);
            str_concat_assoc (G.char_to_str c) (G.render_json_escape escape_result) (String.string_of_list escape_remainder)
          )
      else
        ()

let parse_json_character_completeness (character: G.json_character) :
  Lemma
  (ensures parser_completeness parse_json_character G.render_json_character character)
  =
  let rendered_character = G.render_json_character character in
  match character with
    | G.Character c -> (
      String.list_of_string_of_list [c];
      let c'::tail' = String.list_of_string rendered_character in
      string_of_list_eq tail' []
    )
    | G.EscapedCharacter c escape -> (
      String.list_of_concat (G.char_to_str c) (G.render_json_escape escape);
      String.list_of_string_of_list [c];
      let c'::tail' = String.list_of_string rendered_character in
      str_decompose rendered_character [c] tail';
      String.concat_injective (G.char_to_str c) (G.char_to_str c) (String.string_of_list tail') (G.render_json_escape escape);
      assert (String.string_of_list tail' == G.render_json_escape escape);
      parse_json_escape_completeness escape
    )

let parse_json_character_termination (character: G.json_character) (s: string):
  Lemma
  (ensures (matching_parse_result (G.render_json_character character) ((G.render_json_character character) ^ s) parse_json_character))
  =
  match character with
    | G.Character c -> (
      String.list_of_concat (G.char_to_str c) s;
      String.list_of_string_of_list [c]
    )
    | G.EscapedCharacter c (G.Escape c') -> (
      String.list_of_concat (G.char_to_str c) (G.char_to_str c');
      str_concat_assoc (G.char_to_str c) (G.char_to_str c') s;
      String.list_of_concat (G.char_to_str c) ((G.char_to_str c') ^ s);
      String.list_of_concat (G.char_to_str c') s;
      String.list_of_string_of_list [c];
      String.list_of_string_of_list [c'];
      String.string_of_list_of_string ((G.char_to_str c') ^ s)
    )
    | G.EscapedCharacter c (G.HexCode c' h1 h2 h3 h4) -> (
      let rendered_c = G.char_to_str c in
      let rendered_c' = G.char_to_str c' in
      String.list_of_string_of_list [c];
      String.list_of_string_of_list [c'];
      hex_is_char h1;
      hex_is_char h2;
      hex_is_char h3;
      hex_is_char h4;
      let h1'::[] = String.list_of_string (G.render_json_hex h1) in
      let h2'::[] = String.list_of_string (G.render_json_hex h2) in
      let h3'::[] = String.list_of_string (G.render_json_hex h3) in
      let h4'::[] = String.list_of_string (G.render_json_hex h4) in
      let rendered_h1 = (G.char_to_str h1') in
      let rendered_h2 = (G.char_to_str h2') in
      let rendered_h3 = (G.char_to_str h3') in
      let rendered_h4 = (G.char_to_str h4') in
      String.string_of_list_of_string (G.render_json_hex h1);
      String.string_of_list_of_string (G.render_json_hex h2);
      String.string_of_list_of_string (G.render_json_hex h3);
      String.string_of_list_of_string (G.render_json_hex h4);
      String.list_of_string_of_list [h1'];
      String.list_of_string_of_list [h2'];
      String.list_of_string_of_list [h3'];
      String.list_of_string_of_list [h4'];
      // It suffices to basically treat h1,h2,h3,h4 as chars h1',h2',h3',h4'
      assert (rendered_h1 == G.render_json_hex h1);
      assert (rendered_h2 == G.render_json_hex h2);
      assert (rendered_h3 == G.render_json_hex h3);
      assert (rendered_h4 == G.render_json_hex h4);
      
      // Decompose (render_json_character character) case
      String.list_of_concat rendered_c (rendered_c' ^ rendered_h1 ^ rendered_h2 ^ rendered_h3 ^ rendered_h4);
      String.string_of_list_of_string (rendered_c' ^ rendered_h1 ^ rendered_h2 ^ rendered_h3 ^ rendered_h4);
      String.list_of_concat rendered_c' (rendered_h1 ^ rendered_h2 ^ rendered_h3 ^ rendered_h4);
      String.string_of_list_of_string (rendered_h1 ^ rendered_h2 ^ rendered_h3 ^ rendered_h4);
      String.list_of_concat rendered_h1 (rendered_h2 ^ rendered_h3 ^ rendered_h4);
      String.string_of_list_of_string (rendered_h2 ^ rendered_h3 ^ rendered_h4);
      String.list_of_concat rendered_h2 (rendered_h3 ^ rendered_h4);
      String.string_of_list_of_string (rendered_h3 ^ rendered_h4);
      String.list_of_concat rendered_h3 rendered_h4;
      String.string_of_list_of_string rendered_h4;

      // Decompose (render_json_character character) ^ s case
      str_concat_assoc rendered_c (rendered_c' ^ rendered_h1 ^ rendered_h2 ^ rendered_h3 ^ rendered_h4) s;
      str_concat_assoc rendered_c' (rendered_h1 ^ rendered_h2 ^ rendered_h3 ^ rendered_h4) s;
      str_concat_assoc rendered_h1 (rendered_h2 ^ rendered_h3 ^ rendered_h4) s;
      str_concat_assoc rendered_h2 (rendered_h3 ^ rendered_h4) s;
      str_concat_assoc rendered_h3 rendered_h4 s;
      String.list_of_concat rendered_c (rendered_c' ^ rendered_h1 ^ rendered_h2 ^ rendered_h3 ^ rendered_h4 ^ s);
      String.string_of_list_of_string (rendered_c' ^ rendered_h1 ^ rendered_h2 ^ rendered_h3 ^ rendered_h4 ^ s);
      String.list_of_concat rendered_c' (rendered_h1 ^ rendered_h2 ^ rendered_h3 ^ rendered_h4 ^ s);
      String.string_of_list_of_string (rendered_h1 ^ rendered_h2 ^ rendered_h3 ^ rendered_h4 ^ s);
      String.list_of_concat rendered_h1 (rendered_h2 ^ rendered_h3 ^ rendered_h4 ^ s);
      String.string_of_list_of_string (rendered_h2 ^ rendered_h3 ^ rendered_h4 ^ s);
      String.list_of_concat rendered_h2 (rendered_h3 ^ rendered_h4 ^ s);
      String.string_of_list_of_string (rendered_h3 ^ rendered_h4 ^ s);
      String.list_of_concat rendered_h3 (rendered_h4 ^ s);
      String.string_of_list_of_string (rendered_h4 ^ s);
      String.list_of_concat rendered_h4  s;
      String.string_of_list_of_string s
    )

let rec parse_json_characters (s: list char) : Tot (parser_result G.json_characters) (decreases (length s))= 
  if s = [] then
    { result=G.NoCharacters; remainder=s }
  else
    match parse_json_character s with
      | Some { result=character_result; remainder=character_remainder } -> 
          // Prove recursive termination
          character_render_length character_result;
          assert(String.strlen (G.render_json_character character_result) > 0);
          String.list_of_concat (G.render_json_character character_result) (String.string_of_list character_remainder);
          String.concat_length (G.render_json_character character_result) (String.string_of_list character_remainder);
          String.list_of_string_of_list s;
          String.list_of_string_of_list character_remainder;
          parse_json_character_soundness (String.string_of_list s);
          String.concat_length (G.render_json_character character_result) (String.string_of_list character_remainder);
          let { result=characters_result; remainder=characters_remainder } = parse_json_characters character_remainder in
            {
              result = G.Characters character_result characters_result;
              remainder = characters_remainder
            }
      | None -> { result = G.NoCharacters; remainder = s }

let rec parse_json_characters_soundness (s: string) :
  Lemma
  (ensures (parser_soundness (infallible_to_fallible_parser parse_json_characters) G.render_json_characters s))
  (decreases (String.strlen s))
  =
  String.string_of_list_of_string s;
  if s = "" then
  (
    String.list_of_string_of_list [];
    list_of_string_eq s (String.string_of_list []);
    prepend_empty_is_identity s
  )
  else
    match parse_json_character (String.list_of_string s) with
      | Some { result=character_result; remainder=character_remainder } -> 
          let { result=characters_result; remainder=characters_remainder } = parse_json_characters character_remainder in
          // Prove recursive termination
          character_render_length character_result;
          assert(String.strlen (G.render_json_character character_result) > 0);
          parse_json_character_soundness s;
          String.concat_length (G.render_json_character character_result) (String.string_of_list character_remainder);
          String.list_of_concat (G.render_json_character character_result) (String.string_of_list character_remainder);
          String.list_of_string_of_list character_remainder;
          parse_json_characters_soundness (String.string_of_list character_remainder);
          str_concat_assoc (G.render_json_character character_result) (G.render_json_characters characters_result) (String.string_of_list characters_remainder)
      | None -> (
        prepend_empty_is_identity s
      )

let rec parse_json_characters_completeness (characters: G.json_characters) :
  Lemma
  (ensures (parser_completeness (infallible_to_fallible_parser parse_json_characters) G.render_json_characters characters))
  =
  let rendered_characters = G.render_json_characters characters in
  match characters with
    | G.NoCharacters -> (
      String.list_of_string_of_list [];
      list_of_string_eq rendered_characters (String.string_of_list [])
    )
    | G.Characters c characters' -> (
      character_render_length c;
      String.concat_length (G.render_json_character c) (G.render_json_characters characters');
      String.list_of_concat (G.render_json_character c) (G.render_json_characters characters');
      assert(String.strlen rendered_characters > 0);
      empty_iff_len_zero rendered_characters;
      assert(rendered_characters =!= "");
      // rendered_characters = (render_json_character c) + (render_json_characters characters')
      parse_json_character_termination c (G.render_json_characters characters');
      parse_json_character_completeness c;
      let Some {result=character_result; remainder=character_remainder} = parse_json_character (String.list_of_string rendered_characters) in
      String.list_of_string_of_list character_remainder;
      assert (character_result == c);
      parse_json_character_soundness rendered_characters;
      String.concat_injective 
        (G.render_json_character c) 
        (G.render_json_character character_result) 
        (G.render_json_characters characters') 
        (String.string_of_list character_remainder);
      assert(String.string_of_list character_remainder == G.render_json_characters characters');
      parse_json_characters_completeness characters'
    )

// Parsing a string starting with a rendered json_characters followed by a suffix starting with a quotation mark will terminate at this suffix
// This is a helper lemma for when we will need to parse json_string
let rec parse_json_characters_termination (characters: G.json_characters) (s: string):
  Lemma
  (requires (that_first_char_of s (fun c -> c = G.char_from_codepoint 0x22))) // '"'
  (ensures (matching_parse_result (G.render_json_characters characters) ((G.render_json_characters characters) ^ s) (infallible_to_fallible_parser parse_json_characters)))
  =
  let rendered_characters = G.render_json_characters characters in
  match characters with
    | G.NoCharacters -> (
      String.list_of_string_of_list [];
      list_of_string_eq rendered_characters (String.string_of_list []);
      prepend_empty_is_identity s
    )
    | G.Characters c characters' -> (
      // Handle rendered_characters case
      character_render_length c;
      String.concat_length (G.render_json_character c) (G.render_json_characters characters');
      String.list_of_concat (G.render_json_character c) (G.render_json_characters characters');
      assert(String.strlen rendered_characters > 0);
      empty_iff_len_zero rendered_characters;
      assert(rendered_characters =!= "");
      parse_json_character_termination c (G.render_json_characters characters');
      parse_json_character_completeness c;
      let Some {result=character_result; remainder=character_remainder} = parse_json_character (String.list_of_string rendered_characters) in
      String.list_of_string_of_list character_remainder;
      assert (character_result == c);
      parse_json_character_soundness rendered_characters;
      String.concat_injective 
        (G.render_json_character c)
        (G.render_json_character character_result) 
        (G.render_json_characters characters') 
        (String.string_of_list character_remainder);
      assert(String.string_of_list character_remainder == G.render_json_characters characters');

      // Handle rendered_characters ^ s case
      str_concat_assoc (G.render_json_character c) (G.render_json_characters characters') s;
      String.concat_length (G.render_json_character c) ((G.render_json_characters characters') ^ s);
      String.list_of_concat (G.render_json_character c) ((G.render_json_characters characters') ^ s);
      empty_iff_len_zero (rendered_characters ^ s);
      assert(rendered_characters ^ s =!= "");
      parse_json_character_termination c ((G.render_json_characters characters') ^ s);
      let Some {result=character_result; remainder=character_remainder} = (parse_json_character (String.list_of_string (rendered_characters ^ s))) in
      String.list_of_string_of_list character_remainder;
      parse_json_character_soundness (rendered_characters ^ s);
      String.concat_injective 
        (G.render_json_character c)
        (G.render_json_character character_result)
        ((G.render_json_characters characters') ^ s) 
        (String.string_of_list character_remainder);
      assert(String.string_of_list character_remainder == (G.render_json_characters characters') ^ s);

      // Having got both rendered_characters and rendered_characters ^ s into a decomposed state, invoke the induction hypothesis
      parse_json_characters_termination characters' s
    )

let parse_json_string (s: list char) : option (parser_result G.json_string) =
  match s with
    | [] -> None
    | c::tail -> 
        if c = G.char_from_codepoint 0x22 then // '"'
          let { result=parsed_characters; remainder=remainder_characters } = parse_json_characters tail in
          match remainder_characters with 
            | [] -> None
            | c'::tail' -> 
              if c' = G.char_from_codepoint 0x22 then // '"'
                Some { result = G.String c parsed_characters c'; remainder = tail' }
              else
                None
        else
          None

let parse_json_string_soundness (s: string) :
  Lemma
  (requires (Some? (parse_json_string (String.list_of_string s))))
  (ensures (parser_soundness parse_json_string G.render_json_string s))
  =
  let c::tail = String.list_of_string s in 
  str_decompose s [c] tail;
  String.list_of_string_of_list tail;
  let { result=parsed_characters; remainder=remainder_characters } = parse_json_characters tail in
  String.list_of_string_of_list remainder_characters;
  let c'::tail' = remainder_characters in
  str_decompose (String.string_of_list remainder_characters) [c'] tail';
  assert(c = G.char_from_codepoint 0x22);
  assert(c' = G.char_from_codepoint 0x22);
  parse_json_characters_soundness (String.string_of_list tail);
  // s = c + tail = c + (parsed_characters + remainder_characters) = c + (parsed_characters + (c' + tail'))
  str_concat_assoc (G.render_json_characters parsed_characters) (G.char_to_str c') (String.string_of_list tail');
  str_concat_assoc (G.char_to_str c) ((G.render_json_characters parsed_characters) ^ (G.char_to_str c')) (String.string_of_list tail')

let parse_json_string_completeness (j_string: G.json_string) :
  Lemma
  (ensures (parser_completeness parse_json_string G.render_json_string j_string))
  =
  let rendered_string = G.render_json_string j_string in
  let G.String c characters c' = j_string in
  String.list_of_string_of_list [c];
  String.list_of_string_of_list [c'];
  String.list_of_concat (G.char_to_str c) ((G.render_json_characters characters) ^ (G.char_to_str c'));
  String.list_of_concat (G.render_json_characters characters) (G.char_to_str c');

  let c_::tail_ = String.list_of_string rendered_string in
  assert (c_ == c);
  let { result=parsed_characters; remainder=remainder_characters } = parse_json_characters tail_ in
  String.list_of_string_of_list remainder_characters;
  str_decompose rendered_string [c_] tail_;
  String.concat_injective
    (G.char_to_str c) 
    (G.char_to_str c_) 
    ((G.render_json_characters characters) ^ (G.char_to_str c')) 
    (String.string_of_list tail_);
  assert(((G.render_json_characters characters) ^ (G.char_to_str c')) == String.string_of_list tail_);
  parse_json_characters_termination characters (G.char_to_str c');
  parse_json_characters_completeness characters;
  assert(characters == parsed_characters);
  parse_json_characters_soundness (String.string_of_list tail_);
  String.concat_injective 
    (G.render_json_characters characters) 
    (G.render_json_characters parsed_characters) 
    (G.char_to_str c') 
    (String.string_of_list remainder_characters);
  assert(String.string_of_list remainder_characters == G.char_to_str c')

let parse_json_string_termination (j_string: G.json_string) (s: string):
  Lemma
  (ensures matching_parse_result (G.render_json_string j_string) ((G.render_json_string j_string) ^ s) parse_json_string)
  =
  let rendered_string = G.render_json_string j_string in
  let G.String c characters c' = j_string in
  String.list_of_string_of_list [c];
  String.list_of_string_of_list [c'];

  // Handle (render_json_string j_string) case
  String.list_of_concat (G.char_to_str c) ((G.render_json_characters characters) ^ (G.char_to_str c'));
  String.list_of_concat (G.render_json_characters characters) (G.char_to_str c');
  let c_::tail_ = String.list_of_string rendered_string in
  String.list_of_string_of_list tail_;
  let { result=parsed_characters; remainder=remainder_characters } = parse_json_characters tail_ in
  String.list_of_string_of_list remainder_characters;
  str_decompose rendered_string [c_] tail_;
  String.concat_injective 
    (G.char_to_str c)
    (G.char_to_str c_)
    ((G.render_json_characters characters) ^ (G.char_to_str c')) 
    (String.string_of_list tail_);
  parse_json_characters_termination characters (G.char_to_str c');
  parse_json_characters_completeness characters;
  parse_json_characters_soundness (String.string_of_list tail_);
  String.concat_injective 
    (G.render_json_characters characters) 
    (G.render_json_characters parsed_characters) 
    (G.char_to_str c') 
    (String.string_of_list remainder_characters);

  // Handle (render_json_string j_string) ^ s case
  str_concat_assoc (G.char_to_str c) ((G.render_json_characters characters) ^ (G.char_to_str c')) s;
  str_concat_assoc (G.render_json_characters characters) (G.char_to_str c') s;
  String.list_of_concat (G.char_to_str c) ((G.render_json_characters characters) ^ (G.char_to_str c') ^ s);
  String.list_of_concat (G.render_json_characters characters) ((G.char_to_str c') ^ s);
  String.list_of_concat (G.char_to_str c') s;
  let c_::tail_ = String.list_of_string (rendered_string ^ s) in
  String.list_of_string_of_list tail_;
  let { result=parsed_characters; remainder=remainder_characters } = parse_json_characters tail_ in
  String.list_of_string_of_list remainder_characters;
  str_decompose (rendered_string ^ s) [c_] tail_;
  String.concat_injective
    (G.char_to_str c)
    (G.char_to_str c_)
    ((G.render_json_characters characters) ^ (G.char_to_str c') ^ s)
    (String.string_of_list tail_);
  parse_json_characters_termination characters ((G.char_to_str c') ^ s);
  String.list_of_concat (G.render_json_characters characters) ((G.char_to_str c') ^ s);
  String.list_of_concat (G.char_to_str c')  s;
  parse_json_characters_soundness (String.string_of_list tail_);
  String.concat_injective 
    (G.render_json_characters characters) 
    (G.render_json_characters parsed_characters) 
    ((G.char_to_str c') ^ s) 
    (String.string_of_list remainder_characters)

let rec parse_json_ws_termination (s1 s2: string) :
  Lemma
  // Not whitespace
  (requires (that_first_char_of s2 (fun c -> not(is_char_whitespace c))))
  (ensures matching_parse_result s1 (s1 ^ s2) (infallible_to_fallible_parser parse_json_ws))
  (decreases (String.strlen s1))
  =
  String.list_of_concat s1 s2;
  match String.list_of_string s1 with
    | [] -> ()
    | c::tail -> (
      str_decompose s1 [c] tail;
      str_concat_assoc (G.char_to_str c) (String.string_of_list tail) s2;
      String.list_of_concat (G.char_to_str c) ((String.string_of_list tail) ^ s2);
      String.list_of_string_of_list [c];
      String.list_of_string_of_list tail;
      String.list_of_concat (String.string_of_list tail) s2;
      String.string_of_list_of_string ((String.string_of_list tail) ^ s2);
      let c'::tail' = String.list_of_string (s1 ^ s2) in
      String.list_of_string_of_list tail';
      assert(String.string_of_list tail' == ((String.string_of_list tail) ^ s2));
      str_tail_decrease s1;
      parse_json_ws_termination (String.string_of_list tail) s2
    )

// Utility lemma saying that the parser result remainder will not start with a whitespace.
let rec parse_json_ws_remainder_no_whitespace_prefix (s: string) :
  Lemma
  (ensures (
    let { result=_; remainder=remainder } = parse_json_ws (String.list_of_string s) in
    match remainder with
      | [] -> true
      | c::_ -> not(is_char_whitespace c)
  ))
  (decreases (String.strlen s))
  =
  match String.list_of_string s with
    | [] -> ()
    | c::tail -> (
      String.list_of_string_of_list tail;
      str_tail_decrease s;
      parse_json_ws_remainder_no_whitespace_prefix (String.string_of_list tail)
    )

// Implement mutually recursive parser. To assist with termination proof, all parser results have an extra refinement indicating
// that the remainder part, if it exists, has length at most the length of the input. This is a relaxation of the soundness
// criteria that will be proven next.
//
// Decrease criteria has also been refined to assist FStar into proving termination.
let rec parse_json_value (s: list char) : 
Tot 
(res: option (parser_result G.json_value) {Some? res ==> length ((Some?.v res).remainder) <= length s})
(decreases %[(length s); 1]) =
  match s with
    | [] -> None
    | c::tail -> 
      // Dispatch to the correct parser depending on the next symbol
      if c = G.char_from_codepoint 0x7B then // '{' ... Object
        match parse_json_object s with
          | None -> None
          | Some { result=result; remainder=remainder } -> Some { result=G.ObjectValue result; remainder=remainder }
      else if c = G.char_from_codepoint 0x5B then // '[' ... Array
        match parse_json_array s with
          | None -> None
          | Some { result=result; remainder=remainder } -> Some { result=G.ArrayValue result; remainder=remainder }
      else if c = G.char_from_codepoint 0x22 then // '"' ... String
        match parse_json_string s with
          | None -> None
          | Some { result=result; remainder=remainder } -> (
            // Prove decrease in remainder length
            String.list_of_string_of_list s;
            String.list_of_string_of_list remainder;
            parse_json_string_soundness (String.string_of_list s);
            String.concat_length (G.render_json_string result) (String.string_of_list remainder);
            Some { result=G.StringValue result; remainder=remainder }
          )
      else if c = G.char_from_codepoint 0x74 then // 't' ... "true"
        match s with
          | c1::c2::c3::c4::tail -> 
            // Prove decrease in remainder length
            String.concat_length (String.string_of_list [c1;c2;c3;c4]) (String.string_of_list tail);
            if c1 = G.char_from_codepoint 0x74 && 
                c2 = G.char_from_codepoint 0x72 && 
                c3 = G.char_from_codepoint 0x75 && 
                c4 = G.char_from_codepoint 0x65 
            then
              Some { result=G.BooleanValue "true"; remainder=tail }
            else
              None
          | _ -> None
      else if c = G.char_from_codepoint 0x66 then // 'f' ... "false"
        match s with
          | c1::c2::c3::c4::c5::tail -> 
            if c1 = G.char_from_codepoint 0x66 && 
                c2 = G.char_from_codepoint 0x61 && 
                c3 = G.char_from_codepoint 0x6C && 
                c4 = G.char_from_codepoint 0x73 &&
                c5 = G.char_from_codepoint 0x65
            then
              Some { result=G.BooleanValue "false"; remainder=tail }
            else
              None
          | _ -> None
      else if c = G.char_from_codepoint 0x6E then // 'n' ... "null"
        match s with
          | c1::c2::c3::c4::tail -> 
            if c1 = G.char_from_codepoint 0x6E && 
                c2 = G.char_from_codepoint 0x75 && 
                c3 = G.char_from_codepoint 0x6C && 
                c4 = G.char_from_codepoint 0x6C 
            then
              Some { result=G.NullValue "null"; remainder=tail }
            else
              None
          | _ -> None
      else // Number
        match parse_json_number s with
          | None -> None
          | Some { result=result; remainder=remainder } -> (
              // Prove decrease in remainder length
              String.list_of_string_of_list s;
              String.list_of_string_of_list remainder;
              parse_json_number_soundness (String.string_of_list s);
              String.concat_length (G.render_json_number result) (String.string_of_list remainder);
              Some { result=G.NumberValue result; remainder=remainder }
            )

and
parse_json_object (s: list char) :
Tot
(res: option (parser_result G.json_object) {Some? res ==> length ((Some?.v res).remainder) <= length s})
(decreases %[(length s); 0]) =
  match s with
    | [] -> None
    | c::tail -> 
      if c = G.char_from_codepoint 0x7B then // '{'
        let { result=parsed_ws; remainder=remainder } = parse_json_ws tail in
        // Prove recursive termination by showing decreasing string length
        String.list_of_string_of_list tail;
        String.list_of_string_of_list remainder;
        parse_json_ws_soundness (String.string_of_list tail);
        String.concat_length (G.render_json_ws parsed_ws) (String.string_of_list remainder);
        match remainder with
          | [] -> None
          | c'::tail' -> 
            if c' = G.char_from_codepoint 0x7D then // '}'
              Some { result=G.EmptyObject c parsed_ws c'; remainder=tail'}
            else
              // Not empty object
              match parse_json_members remainder with
                | None -> None
                | Some { result=G.SingletonMember (G.Member _ s ws colon elem); remainder=remainder'} -> 
                (
                  match remainder' with
                    | [] -> None
                    | c''::tail'' ->
                      if c'' = G.char_from_codepoint 0x7D then // '}' 
                        // Optimization to parse whitespace before parsing members
                        Some { result=G.Object c (G.SingletonMember (G.Member parsed_ws s ws colon elem)) c''; remainder = tail'' }
                      else
                        None
                )
                | Some { result=G.Members (G.Member _ s ws colon elem) comma members; remainder=remainder'} -> 
                (
                  match remainder' with
                    | [] -> None
                    | c''::tail'' -> 
                      if c'' = G.char_from_codepoint 0x7D then // '}' 
                        // Optimization to parse whitespace before parsing members
                        Some { result=G.Object c (G.Members (G.Member parsed_ws s ws colon elem) comma members) c''; remainder = tail'' }
                      else
                        None
                )
      else
        None
and
parse_json_members (s: list char) :
Tot
(res: option (parser_result G.json_members) {Some? res ==> length ((Some?.v res).remainder) <= length s})
(decreases %[(length s); 4]) =
  match parse_json_member s with
    | None -> None
    | Some { result=parsed_member; remainder=remainder } -> 
      (
      match remainder with
        | [] -> Some { result=G.SingletonMember parsed_member; remainder=remainder }
        | c::tail -> 
          if c = G.char_from_codepoint 0x2C then // ','
          (
            match parse_json_members tail with
              | None -> None
              | Some { result=parsed_members; remainder=remainder } -> 
                  Some { result = G.Members parsed_member c parsed_members; remainder=remainder }
          )
          else
            Some { result=G.SingletonMember parsed_member; remainder=remainder }
      )
and
parse_json_member (s: list char) : 
  Tot 
  (res: option (parser_result G.json_member) {Some? res ==> length ((Some?.v res).remainder) <= length s}) 
  (decreases %[(length s); 3]) 
  = 
  let { result=parsed_ws; remainder=remainder } = parse_json_ws s in
  String.list_of_string_of_list s;
  String.list_of_string_of_list remainder;
  parse_json_ws_soundness (String.string_of_list s);
  String.concat_length (G.render_json_ws parsed_ws) (String.string_of_list remainder);
  match parse_json_string remainder with
    | None -> None
    | Some { result=parsed_string; remainder=remainder' } -> 
      String.list_of_string_of_list remainder';
      parse_json_string_soundness (String.string_of_list remainder);
      String.concat_length (G.render_json_string parsed_string) (String.string_of_list remainder');
      let { result=parsed_ws'; remainder=remainder'' } = parse_json_ws remainder' in
      String.list_of_string_of_list remainder'';
      parse_json_ws_soundness (String.string_of_list remainder');
      String.concat_length (G.render_json_ws parsed_ws') (String.string_of_list remainder'');
      match remainder'' with
        | [] -> None
        | c::tail ->
          // str_tail_decrease remainder'';
          if c = G.char_from_codepoint 0x3A then // ':'
            match parse_json_element tail with
              | None -> None
              | Some { result=parsed_element; remainder=remainder''' } ->
                  Some {result = G.Member parsed_ws parsed_string parsed_ws' c parsed_element; remainder=remainder''' }
          else
            None
and
parse_json_array (s: list char) :
Tot 
  (res: option (parser_result G.json_array) {Some? res ==> length ((Some?.v res).remainder) <= length s})
  (decreases %[(length s); 0]) 
  = 
  match s with
    | [] -> None
    | c::tail ->
      if c = G.char_from_codepoint 0x5B then // '['
        let { result=parsed_ws; remainder=remainder } = parse_json_ws tail in
        String.list_of_string_of_list tail;
        String.list_of_string_of_list remainder;
        parse_json_ws_soundness (String.string_of_list tail);
        String.concat_length (G.render_json_ws parsed_ws) (String.string_of_list remainder);
        match remainder with
          | [] -> None
          | c'::tail' ->
            if c' = G.char_from_codepoint 0x5D then // ']'
              Some { result=G.EmptyArray c parsed_ws c'; remainder=tail' }
            else
            (
              match parse_json_elements remainder with
                | None -> None
                | Some { result=(G.SingletonElements (G.Element _ v ws)); remainder=remainder' } ->
                  (
                    match remainder' with
                      | [] -> None
                      | c''::tail'' ->
                        if c'' = G.char_from_codepoint 0x5D then // ']'
                          // Optimization to parse whitespace before parsing elements
                          Some { result = G.Array c (G.SingletonElements (G.Element parsed_ws v ws)) c''; remainder = tail'' }
                        else
                          None
                  )
                | Some { result=(G.Elements (G.Element _ v ws) comma elements); remainder=remainder' } ->
                    match remainder' with
                      | [] -> None
                      | c''::tail'' ->
                        if c'' = G.char_from_codepoint 0x5D then // ']'
                          // Optimization to parse whitespace before parsing elements
                          Some { result = G.Array c (G.Elements (G.Element parsed_ws v ws) comma elements) c''; remainder = tail'' }
                        else
                          None
            )
      else
        None
and
parse_json_elements (s: list char) :
Tot
  (res: option (parser_result G.json_elements) {Some? res ==> length ((Some?.v res).remainder) <= length s})
  (decreases %[(length s); 3]) 
  = 
  match parse_json_element s with
    | None -> None
    | Some { result=parsed_element; remainder=remainder } ->
        match remainder with
          | [] -> Some { result=G.SingletonElements parsed_element; remainder=remainder }
          | c::tail ->
              if c = G.char_from_codepoint 0x2C then // ','
                match parse_json_elements tail with
                  | None -> None
                  | Some { result=parsed_elements; remainder=remainder' } ->
                      Some { result=G.Elements parsed_element c parsed_elements; remainder=remainder' }
              else
                Some { result=G.SingletonElements parsed_element; remainder=remainder }
and
parse_json_element (s: list char) : 
  Tot 
  (res: option (parser_result G.json_element) {Some? res ==> length ((Some?.v res).remainder) <= length s}) 
  (decreases %[(length s); 2])
  = 
  let { result=parsed_ws; remainder=remainder } = parse_json_ws s in
  String.list_of_string_of_list s;
  String.list_of_string_of_list remainder;
  parse_json_ws_soundness (String.string_of_list s);
  String.concat_length (G.render_json_ws parsed_ws) (String.string_of_list remainder);
  match parse_json_value remainder with
    | None -> None
    | Some { result=parsed_value; remainder=remainder' } ->
      let { result=parsed_ws'; remainder=remainder'' } = parse_json_ws remainder' in
      String.list_of_string_of_list remainder';
      String.list_of_string_of_list remainder'';
      parse_json_ws_soundness (String.string_of_list remainder');
      String.concat_length (G.render_json_ws parsed_ws') (String.string_of_list remainder'');
      Some { result=G.Element parsed_ws parsed_value parsed_ws'; remainder=remainder'' } 

// Prove recursive soundness
let rec parse_json_value_soundness (s: string) : 
  Lemma (requires (Some? (parse_json_value (String.list_of_string s)))) 
  (ensures (parser_soundness parse_json_value G.render_json_value s)) 
  (decreases %[(String.strlen s); 1])
  = 
  match String.list_of_string s with
    | c::tail -> 
      // Dispatch to the correct parser depending on the next symbol
      if c = G.char_from_codepoint 0x7B then // '{' ... Object
        match parse_json_object (String.list_of_string s) with
          | Some { result=result; remainder=remainder } -> parse_json_object_soundness s
      else if c = G.char_from_codepoint 0x5B then // '[' ... Array
        match parse_json_array (String.list_of_string s) with
          | Some { result=result; remainder=remainder } -> parse_json_array_soundness s
      else if c = G.char_from_codepoint 0x22 then // '"' ... String
        match parse_json_string (String.list_of_string s) with
          | Some { result=result; remainder=remainder } -> parse_json_string_soundness s
      else if c = G.char_from_codepoint 0x74 then // 't' ... "true"
        match String.list_of_string s with
          | c1::c2::c3::c4::tail -> 
            // Prove decrease in remainder length
            str_decompose s [c1;c2;c3;c4] tail;
            String.concat_length (String.string_of_list [c1;c2;c3;c4]) (String.string_of_list tail);
            if c1 = G.char_from_codepoint 0x74 && 
                c2 = G.char_from_codepoint 0x72 && 
                c3 = G.char_from_codepoint 0x75 && 
                c4 = G.char_from_codepoint 0x65 
            then
            (
              string_of_list_eq [c1;c2;c3;c4] (String.list_of_string "true");
              String.string_of_list_of_string "true";
              str_decompose s [c1;c2;c3;c4] tail
            )
            else
              ()
      else if c = G.char_from_codepoint 0x66 then // 'f' ... "false"
        match String.list_of_string s with
          | c1::c2::c3::c4::c5::tail -> 
            // Prove decrease in remainder length
            str_decompose s [c1;c2;c3;c4;c5] tail;
            String.concat_length (String.string_of_list [c1;c2;c3;c4;c5]) (String.string_of_list tail);
            if c1 = G.char_from_codepoint 0x66 && 
                c2 = G.char_from_codepoint 0x61 && 
                c3 = G.char_from_codepoint 0x6C && 
                c4 = G.char_from_codepoint 0x73 &&
                c5 = G.char_from_codepoint 0x65
            then
            (
              string_of_list_eq [c1;c2;c3;c4;c5] (String.list_of_string "false");
              String.string_of_list_of_string "false";
              str_decompose s [c1;c2;c3;c4;c5] tail
            )
            else
              ()
      else if c = G.char_from_codepoint 0x6E then // 'n' ... "null"
        match String.list_of_string s with
          | c1::c2::c3::c4::tail -> 
            // Prove decrease in remainder length
            str_decompose s [c1;c2;c3;c4] tail;
            String.concat_length (String.string_of_list [c1;c2;c3;c4]) (String.string_of_list tail);
            if c1 = G.char_from_codepoint 0x6E && 
                c2 = G.char_from_codepoint 0x75 && 
                c3 = G.char_from_codepoint 0x6C && 
                c4 = G.char_from_codepoint 0x6C 
            then
            (
              string_of_list_eq [c1;c2;c3;c4] (String.list_of_string "null");
              String.string_of_list_of_string "null";
              str_decompose s [c1;c2;c3;c4] tail
            )
            else
              ()
      else // Number
        match parse_json_number (String.list_of_string s) with
          | Some { result=result; remainder=remainder } -> parse_json_number_soundness s
and
parse_json_object_soundness (s: string) : 
  Lemma (requires (Some? (parse_json_object (String.list_of_string s)))) 
  (ensures (parser_soundness parse_json_object G.render_json_object s)) 
  (decreases %[(String.strlen s); 0])
  =
  match String.list_of_string s with
    | c::tail -> 
      if c = G.char_from_codepoint 0x7B then // '{'
        let { result=parsed_ws; remainder=remainder } = parse_json_ws tail in
        str_decompose s [c] tail;
        String.list_of_string_of_list tail;
        String.list_of_string_of_list remainder;
        parse_json_ws_soundness (String.string_of_list tail);
        str_tail_decrease s;
        String.concat_length (G.render_json_ws parsed_ws) (String.string_of_list remainder);
        match remainder with
          | c'::tail' -> 
            str_decompose (String.string_of_list remainder) [c'] tail';
            if c' = G.char_from_codepoint 0x7D then // '}'
            (
              // s = c + (parsed_ws + (c' + tail'))
              str_concat_assoc (G.render_json_ws parsed_ws) (G.char_to_str c') (String.string_of_list tail');
              str_concat_assoc (G.char_to_str c) ((G.render_json_ws parsed_ws) ^ (G.char_to_str c')) (String.string_of_list tail')
            )
            else
              // Not empty object
              let Some { result=parsed_members; remainder=remainder' } = parse_json_members remainder in
              String.list_of_string_of_list remainder';
              parse_json_members_soundness (String.string_of_list remainder);
              match remainder' with
                | c''::tail'' ->
                  // s = c + (parsed_ws + (parsed_members + (c'' + tail'')))
                  str_decompose (String.string_of_list remainder') [c''] tail'';
                  str_concat_assoc (G.render_json_members parsed_members) (G.char_to_str c'') (String.string_of_list tail'');
                  str_concat_assoc (G.render_json_ws parsed_ws) ((G.render_json_members parsed_members) ^ (G.char_to_str c'')) (String.string_of_list tail'');
                  str_concat_assoc (G.char_to_str c) ((G.render_json_ws parsed_ws) ^ (G.render_json_members parsed_members) ^ (G.char_to_str c'')) (String.string_of_list tail'');
                  assert(s == ((G.char_to_str c) ^ (G.render_json_ws parsed_ws) ^ (G.render_json_members parsed_members) ^ (G.char_to_str c'')) ^ (String.string_of_list tail''));
                  parse_json_ws_remainder_no_whitespace_prefix (String.string_of_list tail);
                  if c'' = G.char_from_codepoint 0x7D then // '}' 
                  (
                    // Decompose the case of parsed_members and justify the optimized substitution of parsed_ws as the first whitespace member of members
                    str_concat_assoc (G.render_json_ws parsed_ws) (G.render_json_members parsed_members) (G.char_to_str c'');
                    match parsed_members with
                      | G.SingletonMember (G.Member empty s ws colon elem) -> (
                        assert(empty == G.NoWhitespace);
                        prepend_empty_is_identity ((G.render_json_string s) ^ (G.render_json_ws ws) ^ (G.char_to_str colon) ^ (G.render_json_element elem));
                        assert(G.render_json_members parsed_members == ((G.render_json_string s) ^ (G.render_json_ws ws) ^ (G.char_to_str colon) ^ (G.render_json_element elem)))
                      )
                      | G.Members (G.Member empty s ws colon elem) comma members -> (
                        assert(empty == G.NoWhitespace);
                        prepend_empty_is_identity ((G.render_json_string s) ^ (G.render_json_ws ws) ^ (G.char_to_str colon) ^ (G.render_json_element elem));
                        str_concat_assoc (G.render_json_ws parsed_ws) (G.render_json_member (G.Member empty s ws colon elem)) ((G.char_to_str comma) ^ (G.render_json_members members))
                      )
                  )
                  else
                    ()
      else
        ()
and
parse_json_members_soundness (s: string) : 
  Lemma (requires (Some? (parse_json_members (String.list_of_string s)))) 
  (ensures (parser_soundness parse_json_members G.render_json_members s)) 
  (decreases %[(String.strlen s); 4])
  =
  match parse_json_member (String.list_of_string s) with
    | Some { result=parsed_member; remainder=remainder } -> 
      (
      parse_json_member_soundness s;
      match remainder with
        | [] -> ()
        | c::tail -> 
          if c = G.char_from_codepoint 0x2C then // ','
          (
            // Prove termination
            String.list_of_string_of_list tail;
            String.list_of_string_of_list remainder;
            str_decompose (String.string_of_list remainder) [c] tail;
            match parse_json_members tail with
              | Some { result=parsed_members; remainder=remainder } -> 
                (
                  parse_json_members_soundness (String.string_of_list tail);
                  // s = parsed_member + (c + (parsed_members + remainder))
                  str_concat_assoc (G.char_to_str c) (G.render_json_members parsed_members) (String.string_of_list remainder);
                  str_concat_assoc (G.render_json_member parsed_member) ((G.char_to_str c) ^ (G.render_json_members parsed_members)) (String.string_of_list remainder)
                )
          )
          else
            ()
      )
and
parse_json_member_soundness (s: string) : 
  Lemma (requires (Some? (parse_json_member (String.list_of_string s)))) 
  (ensures (parser_soundness parse_json_member G.render_json_member s)) 
  (decreases %[(String.strlen s); 3])
  =
  let { result=parsed_ws; remainder=remainder } = parse_json_ws (String.list_of_string s) in
  String.list_of_string_of_list remainder;
  parse_json_ws_soundness s;
  String.concat_length (G.render_json_ws parsed_ws) (String.string_of_list remainder);
  match parse_json_string remainder with
    | Some { result=parsed_string; remainder=remainder' } -> 
      String.list_of_string_of_list remainder';
      parse_json_string_soundness (String.string_of_list remainder);
      String.concat_length (G.render_json_string parsed_string) (String.string_of_list remainder');
      let { result=parsed_ws'; remainder=remainder'' } = parse_json_ws remainder' in
      String.list_of_string_of_list remainder'';
      parse_json_ws_soundness (String.string_of_list remainder');
      String.concat_length (G.render_json_ws parsed_ws') (String.string_of_list remainder'');
      match remainder'' with
        | c::tail ->
          String.list_of_string_of_list tail;
          str_decompose (String.string_of_list remainder'') [c] tail;
          if c = G.char_from_codepoint 0x3A then // ':'
            match parse_json_element tail with
              | Some { result=parsed_element; remainder=remainder''' } ->
              (
                  parse_json_element_soundness (String.string_of_list tail);
                  // s = parsed_ws + (parsed_string + (parsed_ws' + (c + (parsed_element + remainder'''))))
                  str_concat_assoc (G.char_to_str c) (G.render_json_element parsed_element) (String.string_of_list remainder''');
                  str_concat_assoc (G.render_json_ws parsed_ws') ((G.char_to_str c) ^ (G.render_json_element parsed_element)) (String.string_of_list remainder''');
                  str_concat_assoc (G.render_json_string parsed_string) ((G.render_json_ws parsed_ws') ^ (G.char_to_str c) ^ (G.render_json_element parsed_element)) (String.string_of_list remainder''');
                  str_concat_assoc (G.render_json_ws parsed_ws) ((G.render_json_string parsed_string) ^ (G.render_json_ws parsed_ws') ^ (G.char_to_str c) ^ (G.render_json_element parsed_element)) (String.string_of_list remainder''')
              )
          else
            ()
and
parse_json_array_soundness (s: string) : 
  Lemma (requires (Some? (parse_json_array (String.list_of_string s)))) 
  (ensures (parser_soundness parse_json_array G.render_json_array s)) 
  (decreases %[(String.strlen s); 0])
  =
  match String.list_of_string s with
    | c::tail ->
      if c = G.char_from_codepoint 0x5B then // '['
        let { result=parsed_ws; remainder=remainder } = parse_json_ws tail in
        String.list_of_string_of_list tail;
        String.list_of_string_of_list remainder;
        str_decompose s [c] tail;
        str_tail_decrease s;
        parse_json_ws_soundness (String.string_of_list tail);
        String.concat_length (G.render_json_ws parsed_ws) (String.string_of_list remainder);
        match remainder with
          | c'::tail' ->
            str_decompose (String.string_of_list remainder) [c'] tail';
            if c' = G.char_from_codepoint 0x5D then // ']'
            (
              // s = c + (parsed_ws + (c' + tail'))
              str_concat_assoc (G.render_json_ws parsed_ws) (G.char_to_str c') (String.string_of_list tail');
              str_concat_assoc (G.char_to_str c) ((G.render_json_ws parsed_ws) ^ (G.char_to_str c')) (String.string_of_list tail')
            )
            else
            (
              let Some { result=parsed_elements; remainder=remainder' } = parse_json_elements remainder in
              String.list_of_string_of_list remainder';
              parse_json_elements_soundness (String.string_of_list remainder);
              let c''::tail'' = remainder' in
              str_decompose (String.string_of_list remainder') [c''] tail'';
              if c'' = G.char_from_codepoint 0x5D then // ']'
              (
                // s = c + (parsed_ws + (parsed_elements + (c'' + tail'')))
                str_concat_assoc (G.render_json_elements parsed_elements) (G.char_to_str c'') (String.string_of_list tail'');
                str_concat_assoc (G.render_json_ws parsed_ws) ((G.render_json_elements parsed_elements) ^ (G.char_to_str c'')) (String.string_of_list tail'');
                str_concat_assoc (G.char_to_str c) ((G.render_json_ws parsed_ws) ^ (G.render_json_elements parsed_elements) ^ (G.char_to_str c'')) (String.string_of_list tail'');
                assert(s == ((G.char_to_str c) ^ (G.render_json_ws parsed_ws) ^ (G.render_json_elements parsed_elements) ^ (G.char_to_str c'')) ^ (String.string_of_list tail''));
                // Justify optimization of substituting parsed_ws into first member of the json_element
                str_concat_assoc (G.render_json_ws parsed_ws) (G.render_json_elements parsed_elements) (G.char_to_str c'');
                parse_json_ws_remainder_no_whitespace_prefix (String.string_of_list tail);
                match parsed_elements with
                  | G.SingletonElements (G.Element empty v ws) -> (
                    assert(empty == G.NoWhitespace);
                    prepend_empty_is_identity ((G.render_json_value v) ^ (G.render_json_ws ws))
                  )
                  | G.Elements (G.Element empty v ws) comma elements -> (
                    assert(empty == G.NoWhitespace);
                    prepend_empty_is_identity ((G.render_json_value v) ^ (G.render_json_ws ws));
                    str_concat_assoc (G.render_json_ws parsed_ws) (G.render_json_element (G.Element empty v ws)) ((G.char_to_str comma) ^ (G.render_json_elements elements))
                  )
              )
              else
                ()
            )
      else
        ()
and
parse_json_elements_soundness (s: string) : 
  Lemma (requires (Some? (parse_json_elements (String.list_of_string s)))) 
  (ensures (parser_soundness parse_json_elements G.render_json_elements s)) 
  (decreases %[(String.strlen s); 3])
  =
  match parse_json_element (String.list_of_string s) with
    | Some { result=parsed_element; remainder=remainder } ->
        parse_json_element_soundness s;
        match remainder with
          | [] -> ()
          | c::tail ->
              // Prove termination
              String.list_of_string_of_list remainder;
              str_decompose (String.string_of_list remainder) [c] tail;
              if c = G.char_from_codepoint 0x2C then // ','
                match parse_json_elements tail with
                  | Some { result=parsed_elements; remainder=remainder' } ->
                    (
                      String.list_of_string_of_list tail;
                      parse_json_elements_soundness (String.string_of_list tail);
                      // s = parsed_element + (c + (parsed_elements + remainder'))
                      str_concat_assoc (G.char_to_str c) (G.render_json_elements parsed_elements) (String.string_of_list remainder');
                      str_concat_assoc (G.render_json_element parsed_element) ((G.char_to_str c) ^ (G.render_json_elements parsed_elements)) (String.string_of_list remainder')
                    )
              else
                ()
and
parse_json_element_soundness (s: string) : 
  Lemma (requires (Some? (parse_json_element (String.list_of_string s)))) 
  (ensures (parser_soundness parse_json_element G.render_json_element s)) 
  (decreases %[(String.strlen s); 2])
  =
  let { result=parsed_ws; remainder=remainder } = parse_json_ws (String.list_of_string s) in
  parse_json_ws_soundness s;
  String.list_of_string_of_list remainder;
  String.concat_length (G.render_json_ws parsed_ws) (String.string_of_list remainder);
  match parse_json_value remainder with
    | Some { result=parsed_value; remainder=remainder' } ->
      String.list_of_string_of_list remainder';
      parse_json_value_soundness (String.string_of_list remainder);
      let { result=parsed_ws'; remainder=remainder'' } = parse_json_ws remainder' in
      String.list_of_string_of_list remainder'';
      parse_json_ws_soundness (String.string_of_list remainder');
      String.concat_length (G.render_json_ws parsed_ws') (String.string_of_list remainder'');
      // s = parsed_ws + (parsed_value + (parsed_ws' + remainder''))
      str_concat_assoc (G.render_json_value parsed_value) (G.render_json_ws parsed_ws') (String.string_of_list remainder'');
      str_concat_assoc (G.render_json_ws parsed_ws) ((G.render_json_value parsed_value) ^ (G.render_json_ws parsed_ws')) (String.string_of_list remainder'')

// Termination proof is causing proving weirdness. Increasing Z3 resources.
#set-options "--z3rlimit 1000"
let rec parse_json_value_termination (value: G.json_value) (s: string):
  Lemma
  (requires (that_first_char_of s (fun c -> is_char_not_json_number_extendable c)))
  (ensures (
    matching_parse_result (G.render_json_value value) ((G.render_json_value value) ^ s) parse_json_value /\
    parser_completeness parse_json_value G.render_json_value value
  ))
  (decreases %[(String.strlen (G.render_json_value value)); 1])
  =
  let rendered_value = G.render_json_value value in
  // Helper lemma to make the proof easier showing that appending s doesn't affect which parser we dispatch to
  start_character_concat rendered_value s;
  match value with
    | G.ObjectValue object -> (
      parse_json_object_termination object s;
      // Prove that object renders into a string starting with '{' which lets us proceed with the object termination proof 
      // We also need to prove that rendered_object^s starts with '{' to make object termination proof useful.
      match object with
        | G.EmptyObject c0 ws c1 -> (
          String.list_of_string_of_list [c0];
          String.list_of_concat (G.char_to_str c0) ((G.render_json_ws ws) ^ (G.char_to_str c1))
        )
        | G.Object c0 members c1 -> (
          String.list_of_string_of_list [c0];
          String.list_of_concat (G.char_to_str c0) ((G.render_json_members members) ^ (G.char_to_str c1))
        )
    )
    | G.ArrayValue array -> (
      parse_json_array_termination array s;
      // Prove that array renders into a string starting with '[' which lets us proceed with the array termination proof 
      // We also need to prove that rendered_object^s starts with '[' to make array termination proof useful.
      match array with
        | G.EmptyArray c0 ws c1 -> (
          String.list_of_string_of_list [c0];
          String.list_of_concat (G.char_to_str c0) ((G.render_json_ws ws) ^ (G.char_to_str c1))
        )
        | G.Array c0 elems c1 -> (
          String.list_of_string_of_list [c0];
          String.list_of_concat (G.char_to_str c0) ((G.render_json_elements elems) ^ (G.char_to_str c1))
        )
    )
    | G.StringValue j_string -> (
      parse_json_string_termination j_string s;
      postpend_empty_is_identity (G.render_json_string j_string);
      parse_json_string_completeness j_string;

      let G.String c0 chars c1 = j_string in 
      String.list_of_string_of_list [c0];
      String.list_of_concat (G.char_to_str c0) ((G.render_json_characters chars) ^ (G.char_to_str c1))
    )
    | G.NumberValue number -> (
      parse_json_number_termination number s;
      postpend_empty_is_identity (G.render_json_number number);
      parse_json_number_completeness number;
      json_number_start_character number
    )
    | G.BooleanValue boolean -> (
      String.list_of_concat rendered_value s;
      if boolean = "true" then
      (
        String.list_of_string_of_list ['t';'r';'u';'e'];
        list_of_string_eq boolean (String.string_of_list ['t';'r';'u';'e']);
        let c1::c2::c3::c4::tail = String.list_of_string rendered_value in
        string_of_list_eq tail []
      )
      else
      (
        String.list_of_string_of_list ['f';'a';'l';'s';'e'];
        list_of_string_eq boolean (String.string_of_list ['f';'a';'l';'s';'e']);
        let c1::c2::c3::c4::c5::tail = String.list_of_string rendered_value in
        string_of_list_eq tail []
      )
    )
    | G.NullValue null -> (
        String.list_of_concat null s;
        String.list_of_string_of_list ['n';'u';'l';'l'];
        list_of_string_eq null (String.string_of_list ['n';'u';'l';'l']);
        let c1::c2::c3::c4::tail = String.list_of_string rendered_value in
        string_of_list_eq tail []
    )
and
parse_json_object_termination (object: G.json_object) (s: string):
  Lemma
  (ensures (
    matching_parse_result (G.render_json_object object) ((G.render_json_object object) ^ s) parse_json_object /\
    parser_completeness parse_json_object G.render_json_object object
  ))
  (decreases %[(String.strlen (G.render_json_object object)); 0])
  =
  let rendered_object = G.render_json_object object in
  match object with
    | G.EmptyObject c0 ws c1 -> (
      String.list_of_string_of_list [c0];
      String.list_of_string_of_list [c1];
      // Handle G.render_json_object object case
      String.list_of_concat (G.char_to_str c0) ((G.render_json_ws ws) ^ (G.char_to_str c1));
      String.string_of_list_of_string ((G.render_json_ws ws) ^ (G.char_to_str c1));
      parse_json_ws_termination (G.render_json_ws ws) (G.char_to_str c1);
      String.list_of_concat (G.render_json_ws ws) (G.char_to_str c1);
      parse_json_ws_completeness ws;
      parse_json_ws_soundness ((G.render_json_ws ws) ^ (G.char_to_str c1));
      let { result=parsed_ws; remainder=remainder } = parse_json_ws (String.list_of_string ((G.render_json_ws ws) ^ (G.char_to_str c1))) in
      String.list_of_string_of_list remainder;
      String.concat_injective (G.render_json_ws ws) (G.render_json_ws parsed_ws) (G.char_to_str c1) (String.string_of_list remainder);
      assert(String.string_of_list remainder == (G.char_to_str c1));
      let c'::tail' = remainder in
      string_of_list_eq tail' []; // Finish completeness proof

      // Handle (G.render_json_object object) ^ s case
      str_concat_assoc (G.char_to_str c0) ((G.render_json_ws ws) ^ (G.char_to_str c1)) s;
      str_concat_assoc (G.render_json_ws ws) (G.char_to_str c1) s;
      String.list_of_concat (G.char_to_str c1) s;
      String.list_of_concat (G.char_to_str c0) ((G.render_json_ws ws) ^ (G.char_to_str c1) ^ s);
      String.string_of_list_of_string ((G.render_json_ws ws) ^ (G.char_to_str c1) ^ s);
      parse_json_ws_termination (G.render_json_ws ws) ((G.char_to_str c1) ^ s);
      String.list_of_concat (G.render_json_ws ws) ((G.char_to_str c1) ^ s);
      parse_json_ws_soundness ((G.render_json_ws ws) ^ (G.char_to_str c1) ^ s);
      let { result=parsed_ws; remainder=remainder } = parse_json_ws (String.list_of_string ((G.render_json_ws ws) ^ (G.char_to_str c1) ^ s)) in
      String.list_of_string_of_list remainder;
      String.concat_injective (G.render_json_ws ws) (G.render_json_ws parsed_ws) ((G.char_to_str c1) ^ s) (String.string_of_list remainder);
      assert(String.string_of_list remainder == (G.char_to_str c1) ^ s)
    )
    | G.Object c0 members c1 -> (
      String.list_of_string_of_list [c0];
      String.list_of_string_of_list [c1];
      // Handle G.render_json_object object case
      String.list_of_concat (G.char_to_str c0) ((G.render_json_members members) ^ (G.char_to_str c1));
      String.concat_length (G.char_to_str c0) ((G.render_json_members members) ^ (G.char_to_str c1));
      String.string_of_list_of_string ((G.render_json_members members) ^ (G.char_to_str c1));
      String.list_of_concat (G.render_json_members members) (G.char_to_str c1);
      let { result=parsed_ws; remainder=remainder } = parse_json_ws (String.list_of_string ((G.render_json_members members) ^ (G.char_to_str c1))) in
      String.list_of_string_of_list remainder;

      // Handle G.render_json_object ^ s object case
      str_concat_assoc (G.char_to_str c0) ((G.render_json_members members) ^ (G.char_to_str c1)) s;
      str_concat_assoc (G.render_json_members members) (G.char_to_str c1) s;
      String.list_of_concat (G.char_to_str c0) ((G.render_json_members members) ^ (G.char_to_str c1) ^ s);
      String.string_of_list_of_string ((G.render_json_members members) ^ (G.char_to_str c1) ^ s);
      String.list_of_concat (G.render_json_members members) ((G.char_to_str c1) ^ s);
      let { result=parsed_ws_s; remainder=remainder_s } = parse_json_ws (String.list_of_string ((G.render_json_members members) ^ (G.char_to_str c1) ^ s)) in
      String.list_of_string_of_list remainder_s;

      // Decompose member into parts
      match members with
        | G.SingletonMember (G.Member ws0 str ws1 colon elem) -> (
          // Handle G.render_json_object object case
          str_concat_assoc (G.render_json_ws ws0) ((G.render_json_string str) ^ (G.render_json_ws ws1) ^ (G.char_to_str colon) ^ (G.render_json_element elem)) (G.char_to_str c1);
          // Prep for json_ws termination by proving start character is a quote from the string
          str_concat_assoc (G.render_json_string str) ((G.render_json_ws ws1) ^ (G.char_to_str colon) ^ (G.render_json_element elem)) (G.char_to_str c1);
          json_string_start_character str;
          start_character_concat (G.render_json_string str) (((G.render_json_ws ws1) ^ (G.char_to_str colon) ^ (G.render_json_element elem)) ^ (G.char_to_str c1));
          parse_json_ws_termination (G.render_json_ws ws0) (((G.render_json_string str) ^ (G.render_json_ws ws1) ^ (G.char_to_str colon) ^ (G.render_json_element elem)) ^ (G.char_to_str c1));
          String.list_of_concat (G.render_json_ws ws0) (((G.render_json_string str) ^ (G.render_json_ws ws1) ^ (G.char_to_str colon) ^ (G.render_json_element elem)) ^ (G.char_to_str c1));
          parse_json_ws_completeness ws0;
          parse_json_ws_soundness ((G.render_json_ws ws0) ^ (((G.render_json_string str) ^ (G.render_json_ws ws1) ^ (G.char_to_str colon) ^ (G.render_json_element elem)) ^ (G.char_to_str c1)));
          String.concat_injective (G.render_json_ws ws0) (G.render_json_ws parsed_ws) (((G.render_json_string str) ^ (G.render_json_ws ws1) ^ (G.char_to_str colon) ^ (G.render_json_element elem)) ^ (G.char_to_str c1)) (String.string_of_list remainder);
          String.concat_length (G.render_json_ws parsed_ws) (String.string_of_list remainder);
          // Sanity check
          assert(parsed_ws == ws0);
          assert(String.string_of_list remainder == (((G.render_json_string str) ^ (G.render_json_ws ws1) ^ (G.char_to_str colon) ^ (G.render_json_element elem)) ^ (G.char_to_str c1)));
          // Prep for json_members termination
          assert(String.strlen (String.string_of_list remainder) < String.strlen rendered_object);
          String.concat_length ((G.render_json_string str) ^ (G.render_json_ws ws1) ^ (G.char_to_str colon) ^ (G.render_json_element elem)) (G.char_to_str c1);
          assert(String.strlen ((G.render_json_string str) ^ (G.render_json_ws ws1) ^ (G.char_to_str colon) ^ (G.render_json_element elem)) < String.strlen rendered_object);
          // Force this part of the string into a valid json_members element
          prepend_empty_is_identity ((G.render_json_string str) ^ (G.render_json_ws ws1) ^ (G.char_to_str colon) ^ (G.render_json_element elem));
          parse_json_members_termination (G.SingletonMember (G.Member G.NoWhitespace str ws1 colon elem)) (G.char_to_str c1);
          String.list_of_concat ((G.render_json_string str) ^ (G.render_json_ws ws1) ^ (G.char_to_str colon) ^ (G.render_json_element elem)) (G.char_to_str c1);
          parse_json_members_soundness (String.string_of_list remainder);
          let Some { result=parsed_members; remainder=remainder' } = parse_json_members remainder in
          String.list_of_string_of_list remainder';
          let G.SingletonMember (G.Member ws0' str' ws1' colon' elem') = parsed_members in
          assert(ws0' = G.NoWhitespace); // Sanity check completeness proof
          assert(str = str');
          assert(ws1 = ws1');
          assert(colon = colon');
          assert(elem = elem');
          String.concat_injective 
            ((G.render_json_string str) ^ (G.render_json_ws ws1) ^ (G.char_to_str colon) ^ (G.render_json_element elem))
            (G.render_json_members parsed_members)
            (G.char_to_str c1)
            (String.string_of_list remainder');
          assert(String.string_of_list remainder' = G.char_to_str c1);
          assert(parser_completeness parse_json_object G.render_json_object object);

          // Handle G.render_json_object ^ s object case
          str_concat_assoc (G.render_json_ws ws0) ((G.render_json_string str) ^ (G.render_json_ws ws1) ^ (G.char_to_str colon) ^ (G.render_json_element elem)) ((G.char_to_str c1) ^ s);
          str_concat_assoc (G.render_json_string str) ((G.render_json_ws ws1) ^ (G.char_to_str colon) ^ (G.render_json_element elem)) ((G.char_to_str c1) ^ s);
          start_character_concat (G.render_json_string str) (((G.render_json_ws ws1) ^ (G.char_to_str colon) ^ (G.render_json_element elem)) ^ ((G.char_to_str c1) ^ s));
          parse_json_ws_termination (G.render_json_ws ws0) (((G.render_json_string str) ^ (G.render_json_ws ws1) ^ (G.char_to_str colon) ^ (G.render_json_element elem)) ^ ((G.char_to_str c1) ^ s));
          String.list_of_concat (G.render_json_ws ws0) (((G.render_json_string str) ^ (G.render_json_ws ws1) ^ (G.char_to_str colon) ^ (G.render_json_element elem)) ^ ((G.char_to_str c1) ^ s));
          parse_json_ws_soundness ((G.render_json_ws ws0) ^ (((G.render_json_string str) ^ (G.render_json_ws ws1) ^ (G.char_to_str colon) ^ (G.render_json_element elem)) ^ ((G.char_to_str c1) ^ s)));
          String.concat_injective (G.render_json_ws ws0) (G.render_json_ws parsed_ws_s) (((G.render_json_string str) ^ (G.render_json_ws ws1) ^ (G.char_to_str colon) ^ (G.render_json_element elem)) ^ ((G.char_to_str c1) ^ s)) (String.string_of_list remainder_s);
          String.concat_length (G.render_json_ws parsed_ws_s) (String.string_of_list remainder_s);
          String.concat_length ((G.render_json_string str) ^ (G.render_json_ws ws1) ^ (G.char_to_str colon) ^ (G.render_json_element elem)) ((G.char_to_str c1) ^ s);
          String.list_of_concat (G.char_to_str c1) s;
          parse_json_members_termination (G.SingletonMember (G.Member G.NoWhitespace str ws1 colon elem)) ((G.char_to_str c1) ^ s);
          String.list_of_concat ((G.render_json_string str) ^ (G.render_json_ws ws1) ^ (G.char_to_str colon) ^ (G.render_json_element elem)) ((G.char_to_str c1) ^ s);
          parse_json_members_soundness (String.string_of_list remainder_s);
          let Some { result=parsed_members_s; remainder=remainder_s' } = parse_json_members remainder_s in
          String.list_of_string_of_list remainder_s';
          String.concat_injective 
            ((G.render_json_string str) ^ (G.render_json_ws ws1) ^ (G.char_to_str colon) ^ (G.render_json_element elem))
            (G.render_json_members parsed_members_s)
            ((G.char_to_str c1) ^ s)
            (String.string_of_list remainder_s');
          String.list_of_concat (G.char_to_str c1) s
        )
        | G.Members (G.Member ws0 str ws1 colon elem) comma members' -> (
          // Basically the same proof as the SingletonMember case with some rearranging
          // Handle G.render_json_object object case
          str_concat_assoc (G.render_json_ws ws0) ((G.render_json_string str) ^ (G.render_json_ws ws1) ^ (G.char_to_str colon) ^ (G.render_json_element elem)) ((G.char_to_str comma) ^ G.render_json_members members');
          str_concat_assoc (G.render_json_ws ws0) (((G.render_json_string str) ^ (G.render_json_ws ws1) ^ (G.char_to_str colon) ^ (G.render_json_element elem)) ^ ((G.char_to_str comma) ^ G.render_json_members members')) (G.char_to_str c1);
          str_concat_assoc (G.render_json_string str) ((G.render_json_ws ws1) ^ (G.char_to_str colon) ^ (G.render_json_element elem)) ((G.char_to_str comma) ^ G.render_json_members members');
          str_concat_assoc (G.render_json_string str) (((G.render_json_ws ws1) ^ (G.char_to_str colon) ^ (G.render_json_element elem)) ^ ((G.char_to_str comma) ^ G.render_json_members members')) (G.char_to_str c1);

          // Prep for json_ws termination by proving start character is a quote from the string
          json_string_start_character str;
          start_character_concat (G.render_json_string str) ((((G.render_json_ws ws1) ^ (G.char_to_str colon) ^ (G.render_json_element elem)) ^ ((G.char_to_str comma) ^ G.render_json_members members')) ^ (G.char_to_str c1));
          parse_json_ws_termination (G.render_json_ws ws0) ((((G.render_json_string str) ^ (G.render_json_ws ws1) ^ (G.char_to_str colon) ^ (G.render_json_element elem)) ^ ((G.char_to_str comma) ^ G.render_json_members members')) ^ (G.char_to_str c1));
          String.list_of_concat (G.render_json_ws ws0) ((((G.render_json_string str) ^ (G.render_json_ws ws1) ^ (G.char_to_str colon) ^ (G.render_json_element elem)) ^ ((G.char_to_str comma) ^ G.render_json_members members')) ^ (G.char_to_str c1));
          parse_json_ws_completeness ws0;
          parse_json_ws_soundness ((G.render_json_ws ws0) ^ ((((G.render_json_string str) ^ (G.render_json_ws ws1) ^ (G.char_to_str colon) ^ (G.render_json_element elem)) ^ ((G.char_to_str comma) ^ G.render_json_members members')) ^ (G.char_to_str c1)));
          String.concat_injective 
            (G.render_json_ws ws0) 
            (G.render_json_ws parsed_ws) 
            ((((G.render_json_string str) ^ (G.render_json_ws ws1) ^ (G.char_to_str colon) ^ (G.render_json_element elem)) ^ ((G.char_to_str comma) ^ G.render_json_members members')) ^ (G.char_to_str c1))
            (String.string_of_list remainder);
          String.concat_length (G.render_json_ws parsed_ws) (String.string_of_list remainder);
          // Sanity check
          assert(parsed_ws == ws0);
          assert(String.string_of_list remainder == ((((G.render_json_string str) ^ (G.render_json_ws ws1) ^ (G.char_to_str colon) ^ (G.render_json_element elem)) ^ ((G.char_to_str comma) ^ G.render_json_members members')) ^ (G.char_to_str c1)));
          // Prep for json_members termination
          assert(String.strlen (String.string_of_list remainder) < String.strlen rendered_object);
          String.concat_length (((G.render_json_string str) ^ (G.render_json_ws ws1) ^ (G.char_to_str colon) ^ (G.render_json_element elem)) ^ ((G.char_to_str comma) ^ G.render_json_members members')) (G.char_to_str c1);
          assert(String.strlen (((G.render_json_string str) ^ (G.render_json_ws ws1) ^ (G.char_to_str colon) ^ (G.render_json_element elem)) ^ ((G.char_to_str comma) ^ G.render_json_members members')) < String.strlen rendered_object);
          // Force this part of the string into a valid json_members element
          prepend_empty_is_identity ((G.render_json_string str) ^ (G.render_json_ws ws1) ^ (G.char_to_str colon) ^ (G.render_json_element elem));
          parse_json_members_termination (G.Members (G.Member G.NoWhitespace str ws1 colon elem) comma members') (G.char_to_str c1);
          String.list_of_concat (((G.render_json_string str) ^ (G.render_json_ws ws1) ^ (G.char_to_str colon) ^ (G.render_json_element elem)) ^ ((G.char_to_str comma) ^ G.render_json_members members')) (G.char_to_str c1);
          parse_json_members_soundness (String.string_of_list remainder);
          let Some { result=parsed_members; remainder=remainder' } = parse_json_members remainder in
          String.list_of_string_of_list remainder';
          let G.Members (G.Member ws0' str' ws1' colon' elem') comma' members'' = parsed_members in
          assert(ws0' = G.NoWhitespace); // Sanity check completeness proof
          assert(str = str');
          assert(ws1 = ws1');
          assert(colon = colon');
          assert(elem = elem');
          assert(comma = comma');
          assert(members' = members'');

          String.concat_injective 
            (((G.render_json_string str) ^ (G.render_json_ws ws1) ^ (G.char_to_str colon) ^ (G.render_json_element elem)) ^ ((G.char_to_str comma) ^ G.render_json_members members'))
            (G.render_json_members parsed_members)
            (G.char_to_str c1)
            (String.string_of_list remainder');
          assert(String.string_of_list remainder' = G.char_to_str c1);
          assert(parser_completeness parse_json_object G.render_json_object object);

          // Handle G.render_json_object ^ s object case
          str_concat_assoc (G.render_json_ws ws0) (((G.render_json_string str) ^ (G.render_json_ws ws1) ^ (G.char_to_str colon) ^ (G.render_json_element elem)) ^ ((G.char_to_str comma) ^ G.render_json_members members')) ((G.char_to_str c1) ^ s);
          str_concat_assoc (G.render_json_string str) (((G.render_json_ws ws1) ^ (G.char_to_str colon) ^ (G.render_json_element elem)) ^ ((G.char_to_str comma) ^ G.render_json_members members')) ((G.char_to_str c1) ^ s);
          start_character_concat (G.render_json_string str) ((((G.render_json_ws ws1) ^ (G.char_to_str colon) ^ (G.render_json_element elem)) ^ ((G.char_to_str comma) ^ G.render_json_members members')) ^ (G.char_to_str c1) ^ s);
          parse_json_ws_termination (G.render_json_ws ws0) ((((G.render_json_string str) ^ (G.render_json_ws ws1) ^ (G.char_to_str colon) ^ (G.render_json_element elem)) ^ ((G.char_to_str comma) ^ G.render_json_members members')) ^ (G.char_to_str c1) ^ s);
          String.list_of_concat (G.render_json_ws ws0) ((((G.render_json_string str) ^ (G.render_json_ws ws1) ^ (G.char_to_str colon) ^ (G.render_json_element elem)) ^ ((G.char_to_str comma) ^ G.render_json_members members')) ^ (G.char_to_str c1) ^ s);
          parse_json_ws_soundness ((G.render_json_ws ws0) ^ ((((G.render_json_string str) ^ (G.render_json_ws ws1) ^ (G.char_to_str colon) ^ (G.render_json_element elem)) ^ ((G.char_to_str comma) ^ G.render_json_members members')) ^ (G.char_to_str c1) ^ s));
          String.concat_injective 
            (G.render_json_ws ws0) 
            (G.render_json_ws parsed_ws_s) 
            ((((G.render_json_string str) ^ (G.render_json_ws ws1) ^ (G.char_to_str colon) ^ (G.render_json_element elem)) ^ ((G.char_to_str comma) ^ G.render_json_members members')) ^ (G.char_to_str c1) ^ s)
            (String.string_of_list remainder_s);
          String.concat_length (G.render_json_ws parsed_ws_s) (String.string_of_list remainder_s);
          String.list_of_concat (G.char_to_str c1) s;
          parse_json_members_termination (G.Members (G.Member G.NoWhitespace str ws1 colon elem) comma members') ((G.char_to_str c1) ^ s);
          String.list_of_concat (((G.render_json_string str) ^ (G.render_json_ws ws1) ^ (G.char_to_str colon) ^ (G.render_json_element elem)) ^ ((G.char_to_str comma) ^ G.render_json_members members')) ((G.char_to_str c1) ^ s);
          parse_json_members_soundness (String.string_of_list remainder_s);
          let Some { result=parsed_members_s; remainder=remainder_s' } = parse_json_members remainder_s in
          String.list_of_string_of_list remainder_s';
          String.concat_injective 
            (((G.render_json_string str) ^ (G.render_json_ws ws1) ^ (G.char_to_str colon) ^ (G.render_json_element elem)) ^ ((G.char_to_str comma) ^ G.render_json_members members'))
            (G.render_json_members parsed_members_s)
            ((G.char_to_str c1) ^ s)
            (String.string_of_list remainder_s')
        )
    )
and
parse_json_members_termination (members: G.json_members) (s: string):
  Lemma
  (requires (that_first_char_of s (fun c -> 
    not(c = G.char_from_codepoint 0x2C) && // ','
    not(is_char_whitespace c) &&
    is_char_not_json_number_extendable c
  ))) 
  (ensures (
    matching_parse_result (G.render_json_members members) ((G.render_json_members members) ^ s) parse_json_members /\
    parser_completeness parse_json_members G.render_json_members members
  ))
  (decreases %[(String.strlen (G.render_json_members members)); 4])
  =
  let rendered_members = G.render_json_members members in

  String.concat_length rendered_members s;
  String.list_of_concat rendered_members s;
  match members with
    | G.SingletonMember member -> (
      parse_json_member_termination member s;
      let Some { result=parsed_member; remainder=remainder } = parse_json_member (String.list_of_string rendered_members) in
      let Some { result=parsed_member_s; remainder=remainder_s } = parse_json_member (String.list_of_string (rendered_members ^ s)) in
      String.list_of_string_of_list remainder;
      String.list_of_string_of_list remainder_s;

      // list_of_string_eq remainder "";
      parse_json_member_soundness (rendered_members ^ s);
      String.concat_injective
        (G.render_json_member member)
        (G.render_json_member parsed_member_s)
        s
        (String.string_of_list remainder_s)
    )
    | G.Members member comma members' -> (
      // Handle rendered_members case
      str_concat_assoc (G.render_json_member member) (G.char_to_str comma) (G.render_json_members members');
      String.list_of_string_of_list [comma];
      start_character_concat (G.char_to_str comma) (G.render_json_members members');
      String.concat_length (G.render_json_member member) ((G.char_to_str comma) ^ (G.render_json_members members'));
      parse_json_member_termination member ((G.char_to_str comma) ^ (G.render_json_members members'));
      String.list_of_concat (G.render_json_member member) ((G.char_to_str comma) ^ (G.render_json_members members'));
      parse_json_member_soundness ((G.render_json_member member) ^ ((G.char_to_str comma) ^ (G.render_json_members members')));

      let Some { result=parsed_member; remainder=remainder } = parse_json_member (String.list_of_string ((G.render_json_member member) ^ ((G.char_to_str comma) ^ (G.render_json_members members')))) in
      String.list_of_string_of_list remainder;
      String.concat_injective
        (G.render_json_member member)
        (G.render_json_member parsed_member)
        ((G.char_to_str comma) ^ (G.render_json_members members'))
        (String.string_of_list remainder);
      assert(String.string_of_list remainder == ((G.char_to_str comma) ^ (G.render_json_members members')));
      String.list_of_concat (G.char_to_str comma) (G.render_json_members members');
      String.string_of_list_of_string (G.render_json_members members');

      // Handle rendered_members ^ s case
      str_concat_assoc (G.render_json_member member) ((G.char_to_str comma) ^ (G.render_json_members members')) s;
      str_concat_assoc (G.char_to_str comma) (G.render_json_members members') s;
      start_character_concat (G.char_to_str comma) ((G.render_json_members members') ^ s);
      parse_json_member_termination member ((G.char_to_str comma) ^ (G.render_json_members members') ^ s);
      String.list_of_concat (G.render_json_member member) ((G.char_to_str comma) ^ (G.render_json_members members') ^ s);
      parse_json_member_soundness ((G.render_json_member member) ^ ((G.char_to_str comma) ^ (G.render_json_members members') ^ s));
      let Some { result=parsed_member_s; remainder=remainder_s } = parse_json_member (String.list_of_string ((G.render_json_member member) ^ ((G.char_to_str comma) ^ (G.render_json_members members') ^ s))) in
      String.list_of_string_of_list remainder_s;
      String.concat_injective
        (G.render_json_member member)
        (G.render_json_member parsed_member_s)
        ((G.char_to_str comma) ^ (G.render_json_members members') ^ s)
        (String.string_of_list remainder_s);
      String.list_of_concat (G.char_to_str comma) ((G.render_json_members members') ^ s);
      String.string_of_list_of_string ((G.render_json_members members') ^ s);

      parse_json_members_termination members' s
    )
and
parse_json_member_termination (member: G.json_member) (s: string):
  Lemma
  (requires (that_first_char_of s (fun c -> 
    not(is_char_whitespace c) && 
    is_char_not_json_number_extendable c
  )))
  (ensures (
    matching_parse_result (G.render_json_member member) ((G.render_json_member member) ^ s) parse_json_member /\
    parser_completeness parse_json_member G.render_json_member member
  ))
  (decreases %[(String.strlen (G.render_json_member member)); 3])
  =
  let G.Member ws0 str ws1 colon elem = member in
  // Handle rendered_member case
  let { result=parsed_ws; remainder=remainder } = parse_json_ws (String.list_of_string ((G.render_json_ws ws0) ^ (G.render_json_string str) ^ (G.render_json_ws ws1) ^ (G.char_to_str colon) ^ (G.render_json_element elem))) in
  String.list_of_string_of_list remainder;
  json_string_start_character str;
  start_character_concat (G.render_json_string str) ((G.render_json_ws ws1) ^ (G.char_to_str colon) ^ (G.render_json_element elem));
  parse_json_ws_termination (G.render_json_ws ws0) ((G.render_json_string str) ^ (G.render_json_ws ws1) ^ (G.char_to_str colon) ^ (G.render_json_element elem));
  String.list_of_concat (G.render_json_ws ws0) ((G.render_json_string str) ^ (G.render_json_ws ws1) ^ (G.char_to_str colon) ^ (G.render_json_element elem));
  parse_json_ws_completeness ws0;
  parse_json_ws_soundness ((G.render_json_ws ws0) ^ (G.render_json_string str) ^ (G.render_json_ws ws1) ^ (G.char_to_str colon) ^ (G.render_json_element elem));
  String.concat_injective
    (G.render_json_ws ws0)
    (G.render_json_ws parsed_ws)
    ((G.render_json_string str) ^ (G.render_json_ws ws1) ^ (G.char_to_str colon) ^ (G.render_json_element elem))
    (String.string_of_list remainder);
  String.concat_length (G.render_json_ws parsed_ws) (String.string_of_list remainder);

  parse_json_string_termination str ((G.render_json_ws ws1) ^ (G.char_to_str colon) ^ (G.render_json_element elem));
  String.list_of_concat (G.render_json_string str) ((G.render_json_ws ws1) ^ (G.char_to_str colon) ^ (G.render_json_element elem));
  parse_json_string_completeness str;
  parse_json_string_soundness ((G.render_json_string str) ^ (G.render_json_ws ws1) ^ (G.char_to_str colon) ^ (G.render_json_element elem));
  let Some { result=parsed_string; remainder=remainder' } = parse_json_string remainder in
  String.list_of_string_of_list remainder';
  String.concat_injective
    (G.render_json_string str)
    (G.render_json_string parsed_string)
    ((G.render_json_ws ws1) ^ (G.char_to_str colon) ^ (G.render_json_element elem))
    (String.string_of_list remainder');
  String.concat_length (G.render_json_string parsed_string) (String.string_of_list remainder');
  
  let { result=parsed_ws'; remainder=remainder'' } = parse_json_ws remainder' in
  String.list_of_string_of_list remainder'';
  String.list_of_string_of_list [colon];
  start_character_concat (G.char_to_str colon) (G.render_json_element elem);
  parse_json_ws_termination (G.render_json_ws ws1) ((G.char_to_str colon) ^ (G.render_json_element elem));
  String.list_of_concat (G.render_json_ws ws1) ((G.char_to_str colon) ^ (G.render_json_element elem));
  parse_json_ws_completeness ws1;
  parse_json_ws_soundness ((G.render_json_ws ws1) ^ (G.char_to_str colon) ^ (G.render_json_element elem));
  String.concat_injective
    (G.render_json_ws ws1)
    (G.render_json_ws parsed_ws')
    ((G.char_to_str colon) ^ (G.render_json_element elem))
    (String.string_of_list remainder'');
  String.concat_length (G.render_json_ws parsed_ws') (String.string_of_list remainder'');
  
  String.list_of_concat (G.char_to_str colon) (G.render_json_element elem);
  String.concat_length (G.char_to_str colon) (G.render_json_element elem);
  String.string_of_list_of_string (G.render_json_element elem);

  // Handle rendered_member^s case
  str_concat_assoc (G.render_json_ws ws0) ((G.render_json_string str) ^ (G.render_json_ws ws1) ^ (G.char_to_str colon) ^ (G.render_json_element elem)) s;
  str_concat_assoc (G.render_json_string str) ((G.render_json_ws ws1) ^ (G.char_to_str colon) ^ (G.render_json_element elem)) s;
  str_concat_assoc (G.render_json_ws ws1) ((G.char_to_str colon) ^ (G.render_json_element elem)) s;
  str_concat_assoc (G.char_to_str colon) (G.render_json_element elem) s;
  let { result=parsed_ws; remainder=remainder } = parse_json_ws (String.list_of_string ((G.render_json_ws ws0) ^ (G.render_json_string str) ^ (G.render_json_ws ws1) ^ (G.char_to_str colon) ^ (G.render_json_element elem) ^ s)) in
  String.list_of_string_of_list remainder;
  json_string_start_character str;
  start_character_concat (G.render_json_string str) ((G.render_json_ws ws1) ^ (G.char_to_str colon) ^ (G.render_json_element elem) ^ s);
  parse_json_ws_termination (G.render_json_ws ws0) ((G.render_json_string str) ^ (G.render_json_ws ws1) ^ (G.char_to_str colon) ^ (G.render_json_element elem) ^ s);
  String.list_of_concat (G.render_json_ws ws0) ((G.render_json_string str) ^ (G.render_json_ws ws1) ^ (G.char_to_str colon) ^ (G.render_json_element elem) ^ s);
  parse_json_ws_completeness ws0;
  parse_json_ws_soundness ((G.render_json_ws ws0) ^ (G.render_json_string str) ^ (G.render_json_ws ws1) ^ (G.char_to_str colon) ^ (G.render_json_element elem) ^ s);
  String.concat_injective
    (G.render_json_ws ws0)
    (G.render_json_ws parsed_ws)
    ((G.render_json_string str) ^ (G.render_json_ws ws1) ^ (G.char_to_str colon) ^ (G.render_json_element elem) ^ s)
    (String.string_of_list remainder);
  String.concat_length (G.render_json_ws parsed_ws) (String.string_of_list remainder);

  parse_json_string_termination str ((G.render_json_ws ws1) ^ (G.char_to_str colon) ^ (G.render_json_element elem) ^ s);
  String.list_of_concat (G.render_json_string str) ((G.render_json_ws ws1) ^ (G.char_to_str colon) ^ (G.render_json_element elem) ^ s);
  parse_json_string_completeness str;
  parse_json_string_soundness ((G.render_json_string str) ^ (G.render_json_ws ws1) ^ (G.char_to_str colon) ^ (G.render_json_element elem) ^ s);
  let Some { result=parsed_string; remainder=remainder' } = parse_json_string remainder in
  String.list_of_string_of_list remainder';
  String.concat_injective
    (G.render_json_string str)
    (G.render_json_string parsed_string)
    ((G.render_json_ws ws1) ^ (G.char_to_str colon) ^ (G.render_json_element elem) ^ s)
    (String.string_of_list remainder');
  String.concat_length (G.render_json_string parsed_string) (String.string_of_list remainder');
  
  let { result=parsed_ws'; remainder=remainder'' } = parse_json_ws remainder' in
  String.list_of_string_of_list remainder'';
  String.list_of_string_of_list [colon];
  start_character_concat (G.char_to_str colon) ((G.render_json_element elem) ^ s);
  parse_json_ws_termination (G.render_json_ws ws1) ((G.char_to_str colon) ^ (G.render_json_element elem) ^ s);
  String.list_of_concat (G.render_json_ws ws1) ((G.char_to_str colon) ^ (G.render_json_element elem) ^ s);
  parse_json_ws_completeness ws1;
  parse_json_ws_soundness ((G.render_json_ws ws1) ^ (G.char_to_str colon) ^ (G.render_json_element elem) ^ s);
  String.concat_injective
    (G.render_json_ws ws1)
    (G.render_json_ws parsed_ws')
    ((G.char_to_str colon) ^ (G.render_json_element elem) ^ s)
    (String.string_of_list remainder'');
  String.concat_length (G.render_json_ws parsed_ws') (String.string_of_list remainder'');
  
  String.list_of_concat (G.char_to_str colon) ((G.render_json_element elem) ^ s);
  String.concat_length (G.char_to_str colon) ((G.render_json_element elem) ^ s);
  String.string_of_list_of_string ((G.render_json_element elem) ^ s);

  // Invoke final termination/completeness proof
  parse_json_element_termination elem s
and
parse_json_array_termination (array: G.json_array) (s: string) :
  Lemma
  (ensures (
    matching_parse_result (G.render_json_array array) ((G.render_json_array array) ^ s) parse_json_array /\
    parser_completeness parse_json_array G.render_json_array array
  ))
  (decreases %[(String.strlen (G.render_json_array array)); 0])
  =
  let rendered_array = G.render_json_array array in
  match array with
    | G.EmptyArray c0 ws c1 -> (
      // Handle rendered_array case
      String.list_of_string_of_list [c0];
      String.list_of_string_of_list [c1];
      String.list_of_concat (G.char_to_str c0) ((G.render_json_ws ws) ^ (G.char_to_str c1));
      String.string_of_list_of_string ((G.render_json_ws ws) ^ (G.char_to_str c1));

      let { result=parsed_ws; remainder=remainder } = parse_json_ws (String.list_of_string ((G.render_json_ws ws) ^ (G.char_to_str c1))) in
      String.list_of_string_of_list remainder;
      parse_json_ws_termination (G.render_json_ws ws) (G.char_to_str c1);
      String.list_of_concat (G.render_json_ws ws) (G.char_to_str c1);
      parse_json_ws_soundness ((G.render_json_ws ws) ^ (G.char_to_str c1));
      parse_json_ws_completeness ws;
      String.concat_injective
        (G.render_json_ws ws)
        (G.render_json_ws parsed_ws)
        (G.char_to_str c1)
        (String.string_of_list remainder);

      // Handle rendered_array ^ s case
      str_concat_assoc (G.char_to_str c0) ((G.render_json_ws ws) ^ (G.char_to_str c1)) s;
      str_concat_assoc (G.render_json_ws ws) (G.char_to_str c1) s;

      String.list_of_concat (G.char_to_str c0) ((G.render_json_ws ws) ^ (G.char_to_str c1) ^ s);
      String.string_of_list_of_string ((G.render_json_ws ws) ^ (G.char_to_str c1) ^ s);

      let { result=parsed_ws; remainder=remainder } = parse_json_ws (String.list_of_string ((G.render_json_ws ws) ^ (G.char_to_str c1) ^ s)) in
      String.list_of_string_of_list remainder;
      start_character_concat (G.char_to_str c1) s;
      parse_json_ws_termination (G.render_json_ws ws) ((G.char_to_str c1) ^ s);
      String.list_of_concat (G.render_json_ws ws) ((G.char_to_str c1) ^ s);
      parse_json_ws_soundness ((G.render_json_ws ws) ^ (G.char_to_str c1) ^ s);
      String.concat_injective
        (G.render_json_ws ws)
        (G.render_json_ws parsed_ws)
        ((G.char_to_str c1) ^ s)
        (String.string_of_list remainder);
      String.list_of_concat (G.char_to_str c1) s
    )
    | G.Array c0 elems c1 -> (
      String.list_of_string_of_list [c0];
      String.list_of_string_of_list [c1];

      // Handle rendered_array case
      String.list_of_concat (G.char_to_str c0) ((G.render_json_elements elems) ^ (G.char_to_str c1));
      String.concat_length (G.char_to_str c0) ((G.render_json_elements elems) ^ (G.char_to_str c1));
      String.string_of_list_of_string ((G.render_json_elements elems) ^ (G.char_to_str c1));
      let { result=parsed_ws; remainder=remainder } = parse_json_ws (String.list_of_string ((G.render_json_elements elems) ^ (G.char_to_str c1))) in
      parse_json_ws_soundness ((G.render_json_elements elems) ^ (G.char_to_str c1));
      String.concat_length (G.render_json_ws parsed_ws) (String.string_of_list remainder);
      String.list_of_string_of_list remainder;

      // Handle rendered_array ^ s case
      str_concat_assoc (G.char_to_str c0) ((G.render_json_elements elems) ^ (G.char_to_str c1)) s;
      str_concat_assoc (G.render_json_elements elems) (G.char_to_str c1) s;
      String.list_of_concat (G.char_to_str c0) ((G.render_json_elements elems) ^ (G.char_to_str c1) ^ s);
      String.concat_length (G.char_to_str c0) ((G.render_json_elements elems) ^ (G.char_to_str c1) ^ s);
      String.string_of_list_of_string ((G.render_json_elements elems) ^ (G.char_to_str c1) ^ s);
      let { result=parsed_ws_s; remainder=remainder_s } = parse_json_ws (String.list_of_string ((G.render_json_elements elems) ^ (G.char_to_str c1) ^ s)) in
      parse_json_ws_soundness ((G.render_json_elements elems) ^ (G.char_to_str c1) ^ s);
      String.concat_length (G.render_json_ws parsed_ws_s) (String.string_of_list remainder_s);
      String.list_of_string_of_list remainder_s;

      match elems with
        | G.SingletonElements (G.Element ws0 value ws1) -> (
          // Handle rendered_array case
          str_concat_assoc (G.render_json_ws ws0) ((G.render_json_value value) ^ (G.render_json_ws ws1)) (G.char_to_str c1);
          str_concat_assoc (G.render_json_value value) (G.render_json_ws ws1) (G.char_to_str c1);
          json_value_start_character value;
          start_character_concat (G.render_json_value value) ((G.render_json_ws ws1) ^ (G.char_to_str c1));
          parse_json_ws_termination (G.render_json_ws ws0) ((G.render_json_value value) ^ (G.render_json_ws ws1) ^ (G.char_to_str c1));
          String.list_of_concat (G.render_json_ws ws0) ((G.render_json_value value) ^ (G.render_json_ws ws1) ^ (G.char_to_str c1));
          parse_json_ws_completeness ws0;
          String.concat_injective
            (G.render_json_ws ws0)
            (G.render_json_ws parsed_ws)
            ((G.render_json_value value) ^ (G.render_json_ws ws1) ^ (G.char_to_str c1))
            (String.string_of_list remainder);
          assert(String.string_of_list remainder == ((G.render_json_value value) ^ (G.render_json_ws ws1) ^ (G.char_to_str c1)));
          prepend_empty_is_identity ((G.render_json_value value) ^ (G.render_json_ws ws1));
          String.concat_length ((G.render_json_value value) ^ (G.render_json_ws ws1)) (G.char_to_str c1);

          parse_json_elements_termination (G.SingletonElements (G.Element G.NoWhitespace value ws1)) (G.char_to_str c1);
          String.list_of_concat ((G.render_json_value value) ^ (G.render_json_ws ws1)) (G.char_to_str c1);
          parse_json_elements_soundness (String.string_of_list remainder);
          let Some { result=G.SingletonElements (G.Element ws0' value' ws1'); remainder=remainder' } = parse_json_elements remainder in
          String.list_of_string_of_list remainder';
          let parsed_elements = G.SingletonElements (G.Element ws0' value' ws1') in
          // Completeness sanity check
          assert(G.NoWhitespace == ws0');
          assert(value == value');
          assert(ws1 = ws1');
          String.concat_injective
            ((G.render_json_value value) ^ (G.render_json_ws ws1))
            (G.render_json_elements parsed_elements)
            (G.char_to_str c1)
            (String.string_of_list remainder');
          assert(String.string_of_list remainder' == G.char_to_str c1);
          assert(parser_completeness parse_json_array G.render_json_array array);

          // Handle rendered_array ^ s case
          str_concat_assoc (G.render_json_ws ws0) ((G.render_json_value value) ^ (G.render_json_ws ws1)) ((G.char_to_str c1) ^ s);
          str_concat_assoc (G.render_json_value value) (G.render_json_ws ws1) ((G.char_to_str c1) ^ s);
          start_character_concat (G.render_json_value value) ((G.render_json_ws ws1) ^ (G.char_to_str c1) ^ s);
          parse_json_ws_termination (G.render_json_ws ws0) ((G.render_json_value value) ^ (G.render_json_ws ws1) ^ (G.char_to_str c1) ^ s);
          String.list_of_concat (G.render_json_ws ws0) ((G.render_json_value value) ^ (G.render_json_ws ws1) ^ (G.char_to_str c1) ^ s);
          String.concat_injective
            (G.render_json_ws ws0)
            (G.render_json_ws parsed_ws_s)
            ((G.render_json_value value) ^ (G.render_json_ws ws1) ^ (G.char_to_str c1) ^ s)
            (String.string_of_list remainder_s);
          assert(String.string_of_list remainder_s == ((G.render_json_value value) ^ (G.render_json_ws ws1) ^ (G.char_to_str c1) ^ s));

          start_character_concat (G.char_to_str c1) s;
          parse_json_elements_termination (G.SingletonElements (G.Element G.NoWhitespace value ws1)) ((G.char_to_str c1) ^ s);
          String.list_of_concat ((G.render_json_value value) ^ (G.render_json_ws ws1)) ((G.char_to_str c1) ^ s);
          parse_json_elements_soundness (String.string_of_list remainder_s);
          let Some { result=parsed_elements_s; remainder=remainder_s' } = parse_json_elements remainder_s in
          String.list_of_string_of_list remainder_s';
          String.concat_injective
            ((G.render_json_value value) ^ (G.render_json_ws ws1))
            (G.render_json_elements parsed_elements_s)
            ((G.char_to_str c1) ^ s)
            (String.string_of_list remainder_s');
          assert(String.string_of_list remainder_s' == (G.char_to_str c1) ^ s);
          String.list_of_concat (G.char_to_str c1) s
        )
        | G.Elements (G.Element ws0 value ws1) comma elems' -> (
          // Handle rendered_array case
          str_concat_assoc ((G.render_json_ws ws0) ^ (G.render_json_value value) ^ (G.render_json_ws ws1)) ((G.char_to_str comma) ^ (G.render_json_elements elems')) (G.char_to_str c1);
          str_concat_assoc (G.render_json_ws ws0) ((G.render_json_value value) ^ (G.render_json_ws ws1)) ((G.char_to_str comma) ^ (G.render_json_elements elems') ^ (G.char_to_str c1));
          str_concat_assoc (G.char_to_str comma) (G.render_json_elements elems') (G.char_to_str c1);
          str_concat_assoc ((G.render_json_value value) ^ (G.render_json_ws ws1)) ((G.char_to_str comma) ^ (G.render_json_elements elems')) (G.char_to_str c1);

          json_value_start_character value;
          start_character_concat (G.render_json_value value) (G.render_json_ws ws1);
          start_character_concat ((G.render_json_value value) ^ (G.render_json_ws ws1)) (((G.char_to_str comma) ^ (G.render_json_elements elems')) ^ (G.char_to_str c1));
          parse_json_ws_termination (G.render_json_ws ws0) ((((G.render_json_value value) ^ (G.render_json_ws ws1)) ^ ((G.char_to_str comma) ^ (G.render_json_elements elems'))) ^ (G.char_to_str c1));
          String.list_of_concat (G.render_json_ws ws0) ((((G.render_json_value value) ^ (G.render_json_ws ws1)) ^ ((G.char_to_str comma) ^ (G.render_json_elements elems'))) ^ (G.char_to_str c1));
          parse_json_ws_completeness ws0;
          String.concat_injective
            (G.render_json_ws ws0)
            (G.render_json_ws parsed_ws)
            ((((G.render_json_value value) ^ (G.render_json_ws ws1)) ^ ((G.char_to_str comma) ^ (G.render_json_elements elems'))) ^ (G.char_to_str c1))
            (String.string_of_list remainder);
          assert(String.string_of_list remainder == ((((G.render_json_value value) ^ (G.render_json_ws ws1)) ^ ((G.char_to_str comma) ^ (G.render_json_elements elems'))) ^ (G.char_to_str c1)));
          prepend_empty_is_identity ((G.render_json_value value) ^ (G.render_json_ws ws1));

          String.concat_length (((G.render_json_value value) ^ (G.render_json_ws ws1)) ^ ((G.char_to_str comma) ^ (G.render_json_elements elems'))) (G.char_to_str c1);
          parse_json_elements_termination (G.Elements (G.Element G.NoWhitespace value ws1) comma elems') (G.char_to_str c1);
          String.list_of_concat (((G.render_json_value value) ^ (G.render_json_ws ws1)) ^ ((G.char_to_str comma) ^ (G.render_json_elements elems'))) (G.char_to_str c1);
          parse_json_elements_soundness (String.string_of_list remainder);
          let Some { result=G.Elements (G.Element ws0' value' ws1') comma' elems''; remainder=remainder' } = parse_json_elements remainder in
          String.list_of_string_of_list remainder';
          let parsed_elements = G.Elements (G.Element ws0' value' ws1') comma' elems'' in
          // Sanity check completeness
          assert(ws0' == G.NoWhitespace);
          assert(value == value');
          assert(ws1 == ws1');
          assert(comma == comma');
          assert(elems' == elems'');
          String.concat_injective
            (((G.render_json_value value) ^ (G.render_json_ws ws1)) ^ ((G.char_to_str comma) ^ (G.render_json_elements elems')))
            (G.render_json_elements parsed_elements)
            (G.char_to_str c1)
            (String.string_of_list remainder');
            
          assert(parser_completeness parse_json_array G.render_json_array array);

          // Handle rendered_array ^ s case
          str_concat_assoc ((G.render_json_ws ws0) ^ (G.render_json_value value) ^ (G.render_json_ws ws1)) ((G.char_to_str comma) ^ (G.render_json_elements elems')) ((G.char_to_str c1) ^ s);
          str_concat_assoc (G.render_json_ws ws0) ((G.render_json_value value) ^ (G.render_json_ws ws1)) ((G.char_to_str comma) ^ (G.render_json_elements elems') ^ ((G.char_to_str c1) ^ s));
          str_concat_assoc (G.char_to_str comma) (G.render_json_elements elems') ((G.char_to_str c1) ^ s);
          str_concat_assoc ((G.render_json_value value) ^ (G.render_json_ws ws1)) ((G.char_to_str comma) ^ (G.render_json_elements elems')) ((G.char_to_str c1) ^ s);

          start_character_concat ((G.render_json_value value) ^ (G.render_json_ws ws1)) (((G.char_to_str comma) ^ (G.render_json_elements elems')) ^ ((G.char_to_str c1) ^ s));
          parse_json_ws_termination (G.render_json_ws ws0) ((((G.render_json_value value) ^ (G.render_json_ws ws1)) ^ ((G.char_to_str comma) ^ (G.render_json_elements elems'))) ^ ((G.char_to_str c1) ^ s));
          String.list_of_concat (G.render_json_ws ws0) ((((G.render_json_value value) ^ (G.render_json_ws ws1)) ^ ((G.char_to_str comma) ^ (G.render_json_elements elems'))) ^ ((G.char_to_str c1) ^ s));
          String.concat_injective
            (G.render_json_ws ws0)
            (G.render_json_ws parsed_ws_s)
            ((((G.render_json_value value) ^ (G.render_json_ws ws1)) ^ ((G.char_to_str comma) ^ (G.render_json_elements elems'))) ^ ((G.char_to_str c1) ^ s))
            (String.string_of_list remainder_s);
          assert(String.string_of_list remainder_s == ((((G.render_json_value value) ^ (G.render_json_ws ws1)) ^ ((G.char_to_str comma) ^ (G.render_json_elements elems'))) ^ (G.char_to_str c1) ^ s));
          prepend_empty_is_identity ((G.render_json_value value) ^ (G.render_json_ws ws1));

          String.concat_length (((G.render_json_value value) ^ (G.render_json_ws ws1)) ^ ((G.char_to_str comma) ^ (G.render_json_elements elems'))) ((G.char_to_str c1) ^ s);
          start_character_concat (G.char_to_str c1) s;
          parse_json_elements_termination (G.Elements (G.Element G.NoWhitespace value ws1) comma elems') ((G.char_to_str c1) ^ s);
          String.list_of_concat (((G.render_json_value value) ^ (G.render_json_ws ws1)) ^ ((G.char_to_str comma) ^ (G.render_json_elements elems'))) ((G.char_to_str c1) ^ s);
          parse_json_elements_soundness (String.string_of_list remainder_s);
          let Some { result=parsed_elements_s; remainder=remainder_s' } = parse_json_elements remainder_s in
          String.list_of_string_of_list remainder_s';
          String.concat_injective
            (((G.render_json_value value) ^ (G.render_json_ws ws1)) ^ ((G.char_to_str comma) ^ (G.render_json_elements elems')))
            (G.render_json_elements parsed_elements_s)
            ((G.char_to_str c1) ^ s)
            (String.string_of_list remainder_s');
          assert(String.string_of_list remainder_s' == ((G.char_to_str c1) ^ s));
          String.list_of_concat (G.char_to_str c1) s
        )
    )
and
parse_json_elements_termination (elements: G.json_elements) (s: string):
  Lemma
  (requires (that_first_char_of s (fun c -> 
    not(c = G.char_from_codepoint 0x2C) && // ','
    not(is_char_whitespace c) &&
    is_char_not_json_number_extendable c
  ))) 
  (ensures (
    matching_parse_result (G.render_json_elements elements) ((G.render_json_elements elements) ^ s) parse_json_elements /\
    parser_completeness parse_json_elements G.render_json_elements elements
  ))
  (decreases %[(String.strlen (G.render_json_elements elements)); 3])
  =
  let rendered_elements = G.render_json_elements elements in
  match elements with
    | G.SingletonElements elem -> (
      // Handle rendered_elements case
      parse_json_element_termination elem s;
      let Some { result=parsed_element; remainder=remainder } = parse_json_element (String.list_of_string (G.render_json_element elem)) in
      String.list_of_string_of_list remainder;
      assert(parser_completeness parse_json_elements G.render_json_elements elements);
      
      // Handle rendered_elements ^ s case
      parse_json_element_soundness ((G.render_json_element elem) ^ s);
      String.list_of_concat (G.render_json_element elem) s;
      let Some { result=parsed_element_s; remainder=remainder_s } = parse_json_element (String.list_of_string ((G.render_json_element elem) ^ s)) in
      String.list_of_string_of_list remainder_s;
      String.concat_injective
        (G.render_json_element elem)
        (G.render_json_element parsed_element_s)
        s
        (String.string_of_list remainder_s)
    )
    | G.Elements elem comma elems' -> (
      // Handle rendered_elements case
      String.list_of_string_of_list [comma];
      start_character_concat (G.char_to_str comma) (G.render_json_elements elems');
      String.concat_length (G.render_json_element elem) ((G.char_to_str comma) ^ (G.render_json_elements elems'));
      parse_json_element_termination elem ((G.char_to_str comma) ^ (G.render_json_elements elems'));
      String.list_of_concat (G.render_json_element elem) ((G.char_to_str comma) ^ (G.render_json_elements elems'));
      parse_json_element_soundness ((G.render_json_element elem) ^ (G.char_to_str comma) ^ (G.render_json_elements elems'));
      let Some { result=parsed_element; remainder=remainder } = parse_json_element (String.list_of_string rendered_elements) in
      String.list_of_string_of_list remainder;
      String.concat_length (G.render_json_element parsed_element) (String.string_of_list remainder);
      String.concat_injective
        (G.render_json_element elem) 
        (G.render_json_element parsed_element) 
        ((G.char_to_str comma) ^ (G.render_json_elements elems'))
        (String.string_of_list remainder);
      assert(String.string_of_list remainder == ((G.char_to_str comma) ^ (G.render_json_elements elems')));
      String.list_of_concat (G.char_to_str comma) (G.render_json_elements elems');
      String.string_of_list_of_string (G.render_json_elements elems');
      parse_json_elements_termination elems' s;
      assert(parser_completeness parse_json_elements G.render_json_elements elements);

      // Handle rendered_elements ^ s case
      str_concat_assoc (G.render_json_element elem) ((G.char_to_str comma) ^ (G.render_json_elements elems')) s;
      str_concat_assoc (G.char_to_str comma) (G.render_json_elements elems') s;
      start_character_concat (G.char_to_str comma) ((G.render_json_elements elems') ^ s);
      String.concat_length (G.render_json_element elem) ((G.char_to_str comma) ^ (G.render_json_elements elems') ^ s);
      parse_json_element_termination elem ((G.char_to_str comma) ^ (G.render_json_elements elems') ^ s);
      String.list_of_concat (G.render_json_element elem) ((G.char_to_str comma) ^ (G.render_json_elements elems') ^ s);
      parse_json_element_soundness ((G.render_json_element elem) ^ (G.char_to_str comma) ^ (G.render_json_elements elems' ^ s));
      let Some { result=parsed_element; remainder=remainder } = parse_json_element (String.list_of_string (rendered_elements ^ s)) in
      String.list_of_string_of_list remainder;
      String.concat_length (G.render_json_element parsed_element) (String.string_of_list remainder);
      String.concat_injective
        (G.render_json_element elem) 
        (G.render_json_element parsed_element) 
        ((G.char_to_str comma) ^ (G.render_json_elements elems') ^ s)
        (String.string_of_list remainder);
      assert(String.string_of_list remainder == ((G.char_to_str comma) ^ (G.render_json_elements elems') ^ s));
      String.list_of_concat (G.char_to_str comma) ((G.render_json_elements elems') ^ s);
      String.list_of_concat (G.render_json_elements elems') s;
      String.string_of_list_of_string ((G.render_json_elements elems') ^ s)
    )
and
parse_json_element_termination (element: G.json_element) (s: string):
  Lemma
  (requires (that_first_char_of s (fun c -> 
    not(is_char_whitespace c) &&
    is_char_not_json_number_extendable c
  ))) 
  (ensures (
    matching_parse_result (G.render_json_element element) ((G.render_json_element element) ^ s) parse_json_element /\
    parser_completeness parse_json_element G.render_json_element element
  ))
  (decreases %[(String.strlen (G.render_json_element element)); 2])
  =
  let rendered_element = G.render_json_element element in
  let G.Element ws0 value ws1 = element in
  // Handle rendered_element case
  json_value_start_character value;
  start_character_concat (G.render_json_value value) (G.render_json_ws ws1);
  parse_json_ws_termination (G.render_json_ws ws0) ((G.render_json_value value) ^ (G.render_json_ws ws1));
  String.list_of_concat (G.render_json_ws ws0) ((G.render_json_value value) ^ (G.render_json_ws ws1));
  parse_json_ws_soundness ((G.render_json_ws ws0) ^ (G.render_json_value value) ^ (G.render_json_ws ws1));
  parse_json_ws_completeness ws0;
  let { result=parsed_ws; remainder=remainder } = parse_json_ws (String.list_of_string rendered_element) in
  String.list_of_string_of_list remainder;
  String.concat_length (G.render_json_ws parsed_ws) (String.string_of_list remainder);
  String.concat_injective
    (G.render_json_ws ws0)
    (G.render_json_ws parsed_ws)
    ((G.render_json_value value) ^ (G.render_json_ws ws1))
    (String.string_of_list remainder);
  assert(String.string_of_list remainder == ((G.render_json_value value) ^ (G.render_json_ws ws1)));
  String.concat_length (G.render_json_value value) (G.render_json_ws ws1);
  // Prove first character of ws1 is not json_number extendable
  let json_ws_start_character (ws: G.json_ws) : Lemma (ensures (that_first_char_of (G.render_json_ws ws) (fun c -> is_char_not_json_number_extendable c))) =
    match ws with
      | G.NoWhitespace -> list_of_string_eq (G.render_json_ws ws) ""
      | G.Whitespace c ws' -> (
        String.list_of_string_of_list [c];
        String.list_of_concat (G.char_to_str c) (G.render_json_ws ws')
      )
  in
  json_ws_start_character ws1;
  parse_json_value_termination value (G.render_json_ws ws1);
  // !!!
  String.list_of_concat (G.render_json_value value) (G.render_json_ws ws1);
  parse_json_value_soundness ((G.render_json_value value) ^ (G.render_json_ws ws1));
  let Some { result=parsed_value; remainder=remainder' } = parse_json_value remainder in
  // !!!
  String.list_of_string_of_list remainder';
  String.concat_injective
    (G.render_json_value value)
    (G.render_json_value parsed_value)
    (G.render_json_ws ws1)
    (String.string_of_list remainder');
  assert(String.string_of_list remainder' == (G.render_json_ws ws1));
  parse_json_ws_completeness ws1;
  assert(parser_completeness parse_json_element G.render_json_element element);

  // Handle rendered_element ^ s case
  str_concat_assoc (G.render_json_ws ws0) ((G.render_json_value value) ^ (G.render_json_ws ws1)) s;
  str_concat_assoc (G.render_json_value value) (G.render_json_ws ws1) s;
  start_character_concat (G.render_json_value value) ((G.render_json_ws ws1) ^ s);
  parse_json_ws_termination (G.render_json_ws ws0) ((G.render_json_value value) ^ (G.render_json_ws ws1) ^ s);
  String.list_of_concat (G.render_json_ws ws0) ((G.render_json_value value) ^ (G.render_json_ws ws1) ^ s);
  parse_json_ws_soundness ((G.render_json_ws ws0) ^ (G.render_json_value value) ^ (G.render_json_ws ws1) ^ s);
  let { result=parsed_ws; remainder=remainder } = parse_json_ws (String.list_of_string (rendered_element ^ s)) in
  String.list_of_string_of_list remainder;
  String.concat_length (G.render_json_ws parsed_ws) (String.string_of_list remainder);
  String.concat_injective
    (G.render_json_ws ws0)
    (G.render_json_ws parsed_ws)
    ((G.render_json_value value) ^ (G.render_json_ws ws1) ^ s)
    (String.string_of_list remainder);
  assert(String.string_of_list remainder == ((G.render_json_value value) ^ (G.render_json_ws ws1) ^ s));
  String.concat_length (G.render_json_value value) ((G.render_json_ws ws1) ^ s);
  start_character_concat (G.render_json_ws ws1) s;
  prepend_empty_is_identity s;
  parse_json_value_termination value ((G.render_json_ws ws1) ^ s);
  String.list_of_concat (G.render_json_value value) ((G.render_json_ws ws1) ^ s);
  parse_json_value_soundness ((G.render_json_value value) ^ (G.render_json_ws ws1) ^ s);
  let Some { result=parsed_value; remainder=remainder' } = parse_json_value remainder in
  String.list_of_string_of_list remainder';
  String.concat_injective
    (G.render_json_value value)
    (G.render_json_value parsed_value)
    ((G.render_json_ws ws1) ^ s)
    (String.string_of_list remainder');
  assert(String.string_of_list remainder' == (G.render_json_ws ws1) ^ s);
  String.list_of_concat (G.render_json_ws ws1) s;

  parse_json_ws_termination (G.render_json_ws ws1) s

let parse_json_value_completeness (value: G.json_value) :
  Lemma
  (ensures (parser_completeness parse_json_value G.render_json_value value))
  =
  empty_iff_len_zero "";
  parse_json_value_termination value ""

let parse_json_object_completeness (object: G.json_object) :
  Lemma
  (ensures (parser_completeness parse_json_object G.render_json_object object))
  =
  empty_iff_len_zero "";
  parse_json_object_termination object ""
  
let parse_json_members_completeness (members: G.json_members) :
  Lemma
  (ensures (parser_completeness parse_json_members G.render_json_members members))
  =
  empty_iff_len_zero "";
  parse_json_members_termination members ""

let parse_json_member_completeness (member: G.json_member) :
  Lemma
  (ensures (parser_completeness parse_json_member G.render_json_member member))
  =
  empty_iff_len_zero "";
  parse_json_member_termination member ""

let parse_json_array_completeness (array: G.json_array) :
  Lemma
  (ensures (parser_completeness parse_json_array G.render_json_array array))
  =
  empty_iff_len_zero "";
  parse_json_array_termination array ""

let parse_json_elements_completeness (elements: G.json_elements) :
  Lemma
  (ensures (parser_completeness parse_json_elements G.render_json_elements elements))
  =
  empty_iff_len_zero "";
  parse_json_elements_termination elements ""

let parse_json_element_completeness (element: G.json_element) :
  Lemma
  (ensures (parser_completeness parse_json_element G.render_json_element element))
  =
  empty_iff_len_zero "";
  parse_json_element_termination element ""

let parse_json (s: string) : option G.json = 
  let parsed_element = parse_json_element (String.list_of_string s) in
  match parsed_element with
    | Some { result=elem; remainder=remainder } -> 
      if remainder = [] then
        Some (G.JSON elem)
      else
        None
    | None -> None

let parse_json_soundness (s: string) : 
  Lemma (requires (Some? (parse_json s))) 
  (ensures (G.render_json (Some?.v (parse_json s)) == s)) 
  =
  parse_json_element_soundness s;
  String.string_of_list_of_string s;
  let Some { result=elem; remainder=remainder } = parse_json_element (String.list_of_string s) in
  string_of_list_eq remainder (String.list_of_string "");
  postpend_empty_is_identity (G.render_json_element elem)

let parse_json_completeness (js: G.json) :
  Lemma
  (ensures (
    Some? (parse_json (G.render_json js)) /\ 
    js == Some?.v (parse_json (G.render_json js))
  ))
  =
  let G.JSON elem = js in
  parse_json_element_completeness elem