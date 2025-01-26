module Json.Grammar

open FStar.Char
open FStar.UInt32

module Char = FStar.Char
module U32 = FStar.UInt32

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

