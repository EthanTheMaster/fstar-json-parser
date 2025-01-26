module Json.Grammar

open FStar.Char
open FStar.UInt32
open FStar.String

module Char = FStar.Char
module U32 = FStar.UInt32
module String = FStar.String

type char = Char.char

let char_from_codepoint (codepoint: nat{ codepoint < 0xd7ff \/ ((0xe000 <= codepoint) /\ (codepoint <= 0x10ffff))}) : char = Char.char_of_u32 (U32.uint_to_t codepoint)

type
  json_ws: Type =
    | NoWhitespace: json_ws
    | Whitespace:
        (c: char{
          (char_from_codepoint 0x20 = c) || // Space
          (char_from_codepoint 0x0A = c) || // Line feed
          (char_from_codepoint 0x0D = c) || // Carriage return
          (char_from_codepoint 0x09 = c)    // Horizontal tab
        }) ->
        json_ws ->
        json_ws
  and
  json_sign: Type =
    | NoSign: json_sign
    | PlusMinus: (c: char{
      char_from_codepoint 0x2B = c || // '+'
      char_from_codepoint 0x2D = c    // '-'
    }) -> json_sign
  and
  json_onenine: Type =
    | OneNine: (c: char{
      let codepoint = U32.v (Char.u32_of_char c) in
        (0x31 <= codepoint /\ codepoint <= 0x39) // '1'-'9'
    }) -> json_onenine
  and
  json_digit: Type =
    | DigitZero: (c: char{ char_from_codepoint 0x30 = c }) -> json_digit
    | DigitOneNine: json_onenine -> json_digit
  and
  json_hex: Type =
    | HexDigit: json_digit -> json_hex
    | HexAF: (c: char{
      let codepoint = U32.v (Char.u32_of_char c) in
        (0x41 <= codepoint /\ codepoint <= 0x46) \/ // 'A'-'F'
        (0x61 <= codepoint /\ codepoint <= 0x66)    // 'a'-'f'
    }) -> json_hex
  and
  json_escape: Type = 
    | Escape: (c: char{ 
        char_from_codepoint 0x22 = c || // '"'
        char_from_codepoint 0x5C = c || // '\'
        char_from_codepoint 0x62 = c || // 'b' 
        char_from_codepoint 0x66 = c || // 'f'
        char_from_codepoint 0x6E = c || // 'n'
        char_from_codepoint 0x72 = c || // 'r'
        char_from_codepoint 0x74 = c    // 't'
      }) -> json_escape
    | HexCode: 
        (c: char{ char_from_codepoint 0x75 = c }) -> // 'u'
        json_hex -> 
        json_hex -> 
        json_hex -> 
        json_hex ->
        json_escape
  and
  json_digits: Type =
    | DigitsSingle: json_digit -> json_digits
    | Digits: json_digit -> json_digits -> json_digits
  and
  json_fraction: Type =
    | NoFraction: json_fraction
    | Fraction: 
        (c: char{ char_from_codepoint 0x2E = c }) -> // '.'
        json_digits ->
        json_fraction
  and
  json_exponent: Type =
    | NoExponent: json_exponent
    | Exponent: 
        (c: char{
          (char_from_codepoint 0x65 = c) \/ // 'e'
          (char_from_codepoint 0x45 = c)    // 'E'
        }) ->
        json_sign ->
        json_digits ->
        json_exponent
  and
  json_integer: Type =
    | IntDigit: json_digit -> json_integer
    | IntDigits: json_onenine -> json_digits -> json_integer
    | IntNegDigit: 
        (c: char{ char_from_codepoint 0x2D = c }) -> // '-'
        json_digit ->
        json_integer
    | IntNegDigits: 
        (c: char{ char_from_codepoint 0x2D = c }) -> // '-'
        json_onenine ->
        json_digits ->
        json_integer
  and
  json_number: Type =
    | Number: json_integer -> json_fraction -> json_exponent -> json_number
  and
  json_character: Type =
    | Character: 
        // This diverges from the JSON spec as FStar's char type is restricted to a Unicode Scalar Value.
        // https://www.unicode.org/glossary/#unicode_scalar_value
        (c: char{
          ~(char_from_codepoint 0x22 = c) /\ // '"'
          ~(char_from_codepoint 0x5C = c)    // '\'
        }) ->
        json_character
    | EscapedCharacter:
        (c: char{ char_from_codepoint 0x5C = c }) -> // '\'
        json_escape ->
        json_character
  and
  json_characters: Type =
    | NoCharacters: json_characters
    | Characters: json_character -> json_characters -> json_characters
  and
  json_string: Type =
    | String: 
        (c0: char{ char_from_codepoint 0x22 = c0 }) -> // '"'
        json_characters ->
        (c1: char{ char_from_codepoint 0x22 = c1 }) -> // '"'
        json_string
  and
  json_value: Type =
    | ObjectValue: json_object -> json_value
    | ArrayValue: json_array -> json_value
    | StringValue: json_string -> json_value
    | NumberValue: json_number -> json_value
    | BooleanValue: (s: string{ s = "true" || s = "false" }) -> json_value
    | NullValue: (s: string{ s = "null" }) -> json_value
  and
  json_object: Type =
    | EmptyObject:
        (c0: char{ char_from_codepoint 0x7B = c0 }) -> // '{'
        json_ws ->
        (c1: char{ char_from_codepoint 0x7D = c1 }) -> // '}'
        json_object
    | Object:
        (c0: char{ char_from_codepoint 0x7B = c0 }) -> // '{'
        json_members ->
        (c1: char{ char_from_codepoint 0x7D = c1 }) -> // '}'
        json_object
  and
  json_members: Type =
    | SingletonMember: json_member -> json_members
    | Members: 
        json_member ->
        (c: char{ char_from_codepoint 0x2C = c }) -> // ','
        json_members ->
        json_members
  and
  json_member: Type =
    | Member: 
        json_ws -> 
        json_string -> 
        json_ws -> 
        (c: char { char_from_codepoint 0x3A = c }) -> // ':'
        json_element ->
        json_member
  and
  json_array: Type =
    | EmptyArray:
        (c0: char{ char_from_codepoint 0x5B = c0 }) -> // '['
        json_ws ->
        (c1: char{ char_from_codepoint 0x5D = c1 }) -> // ']'
        json_array
    | Array:
        (c0: char{ char_from_codepoint 0x5B = c0 }) -> // '['
        json_elements ->
        (c1: char{ char_from_codepoint 0x5D = c1 }) -> // ']'
        json_array
  and
  json_elements: Type =
    | SingletonElements: json_element -> json_elements
    | Elements:
        json_element ->
        (c: char{ char_from_codepoint 0x2C = c }) -> // ','
        json_elements ->
        json_elements
  and
  json_element: Type =
    | Element: json_ws -> json_value -> json_ws -> json_element
  and
  json: Type =
    | JSON: json_element -> json


(*
  Render functions take production rules from the JSON grammar and expand those rules
  into a string. 
*)

let rec render_json_ws (ws: json_ws) : string = 
  match ws with
    | NoWhitespace -> ""
    | Whitespace c ws' -> String.concat "" [(String.string_of_char c); render_json_ws ws']

let render_json_sign (sign: json_sign) : string =
  match sign with
    | NoSign -> ""
    | PlusMinus c -> String.string_of_char c

let render_json_onenine (x: json_onenine) : string =
  match x with
    | OneNine c -> String.string_of_char c

let render_json_digit (d: json_digit) : string =
  match d with
    | DigitZero c -> String.string_of_char c
    | DigitOneNine d -> render_json_onenine d

let render_json_hex (h: json_hex) : string =
  match h with
    | HexDigit d -> render_json_digit d
    | HexAF c -> String.string_of_char c

let render_json_escape (e: json_escape) : string =
  match e with
    | Escape c -> String.string_of_char c
    | HexCode u h0 h1 h2 h3 -> String.concat "" [
        String.string_of_char u; 
        render_json_hex h0;
        render_json_hex h1;
        render_json_hex h2;
        render_json_hex h3;
      ]

let rec render_json_digits (d: json_digits) : string =
  match d with
    | DigitsSingle d' -> render_json_digit d'
    | Digits d' digits -> String.concat "" [render_json_digit d'; render_json_digits digits]

let render_json_fraction (f: json_fraction) : string =
  match f with
    | NoFraction -> ""
    | Fraction period digits -> String.concat "" [String.string_of_char period; render_json_digits digits]

let render_json_exponent (exp: json_exponent) : string =
  match exp with
    | NoExponent -> ""
    | Exponent e sign digits -> String.concat "" [String.string_of_char e; render_json_sign sign; render_json_digits digits]

let render_json_integer (int: json_integer) : string =
  match int with
    | IntDigit digit -> render_json_digit digit
    | IntDigits onenine digits -> String.concat "" [render_json_onenine onenine; render_json_digits digits]
    | IntNegDigit c digit -> String.concat "" [String.string_of_char c; render_json_digit digit]
    | IntNegDigits c onenine digits -> String.concat "" [String.string_of_char c; render_json_onenine onenine; render_json_digits digits]


let render_json_number (num: json_number) : string =
  match num with
    | Number int frac exp -> String.concat "" [render_json_integer int; render_json_fraction frac; render_json_exponent exp]

let render_json_character (char: json_character) : string =
  match char with
    | Character c -> String.string_of_char c
    | EscapedCharacter c escape -> String.concat "" [String.string_of_char c; render_json_escape escape]

let rec render_json_characters (chars: json_characters) : string =
  match chars with
    | NoCharacters -> ""
    | Characters char chars -> String.concat "" [render_json_character char; render_json_characters chars]

let render_json_string (str: json_string) : string =
  match str with
    | String open_quote chars close_quote -> String.concat "" [String.string_of_char open_quote; render_json_characters chars; String.string_of_char close_quote]

let rec 
  render_json_value (value: json_value) : string = 
    match value with
      | ObjectValue o -> render_json_object o
      | ArrayValue a -> render_json_array a
      | StringValue s -> render_json_string s
      | NumberValue n -> render_json_number n
      | BooleanValue b -> b
      | NullValue null -> null
  and
  render_json_object (obj: json_object) : string =
    match obj with
      | EmptyObject open_brace ws close_brace -> String.concat "" [String.string_of_char open_brace; render_json_ws ws; String.string_of_char close_brace]
      | Object open_brace members close_brace -> String.concat "" [String.string_of_char open_brace; render_json_members members; String.string_of_char close_brace]
  and
  render_json_members (mems: json_members) : string =
    match mems with
      | SingletonMember m -> render_json_member m
      | Members mem comma mems' -> String.concat "" [render_json_member mem; String.string_of_char comma; render_json_members mems']
  and
  render_json_member (mem: json_member) : string =
    match mem with
      | Member ws0 str ws1 colon elem -> String.concat "" [render_json_ws ws0; render_json_string str; render_json_ws ws1; String.string_of_char colon; render_json_element elem]
  and
  render_json_array (arr: json_array) : string =
    match arr with
      | EmptyArray open_bracket ws close_bracket -> String.concat "" [String.string_of_char open_bracket; render_json_ws ws; String.string_of_char close_bracket]
      | Array open_bracket elems close_bracket -> String.concat "" [String.string_of_char open_bracket; render_json_elements elems; String.string_of_char close_bracket]
  and
  render_json_elements (elems: json_elements) : string =
    match elems with
      | SingletonElements elem -> render_json_element elem
      | Elements elem comma elems' -> String.concat "" [render_json_element elem; String.string_of_char comma; render_json_elements elems']
  and
  render_json_element (elem: json_element) : string = 
    match elem with
      | Element ws0 value ws1 -> String.concat "" [render_json_ws ws0; render_json_value value; render_json_ws ws1]

let render_json (x: json) : string = 
  match x with
    | JSON elem -> render_json_element elem