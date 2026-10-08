/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cbor
public import Tests.Harness

/-!
Each reason the decoder can give, reached at least once, with the offset it reports.
-/

@[expose] public section

namespace Tests.Decode
open Cbor

def nestedArrays (depth : Nat) : ByteArray :=
  ⟨Array.replicate depth 0x81⟩ ++ hex "00"

/-- An array declaring a million items, each the single byte `00`. -/
def millionZeros : ByteArray := hex "9a000f4240" ++ ⟨Array.replicate 1000000 0⟩

def arrayLength (input : ByteArray) : Option Nat :=
  match decode input with
  | .ok v => match v.view with
    | .array xs => some xs.length
    | _ => none
  | .error _ => none

def checks : List (String × Bool) := [
  ("empty input", refuses ByteArray.empty .truncated 0),
  ("head cut short", refuses (hex "1903") .truncated 2),
  ("byte string longer than the input", refuses (hex "430102") .lengthExceedsInput 0),
  ("count beyond the bytes remaining", refuses (hex "9a000f424000") .lengthExceedsInput 0),
  ("additional information 28", refuses (hex "1c") .reservedInfo 0),
  ("additional information 31 on an integer", refuses (hex "1f") .reservedInfo 0),
  ("indefinite-length byte string", refuses (hex "5f4100ff") .indefiniteLength 0),
  ("indefinite-length array", refuses (hex "9fff") .indefiniteLength 0),
  ("break code", refuses (hex "ff") .unexpectedBreak 0),
  ("one-byte argument below 24", refuses (hex "1817") .nonMinimalHead 0),
  ("two-byte argument below 256", refuses (hex "1900ff") .nonMinimalHead 0),
  ("four-byte argument below 65536", refuses (hex "1a0000ffff") .nonMinimalHead 0),
  ("eight-byte argument below 2^32", refuses (hex "1b00000000ffffffff") .nonMinimalHead 0),
  ("non-minimal length", refuses (hex "580100") .nonMinimalHead 0),
  ("bignum tag", refuses (hex "c24101") .tag 0),
  ("half-precision float", refuses (hex "f93c00") .float 0),
  ("double-precision float", refuses (hex "fb3ff199999999999a") .float 0),
  ("undefined", refuses (hex "f7") .unsupportedSimple 0),
  ("simple value 16", refuses (hex "f0") .unsupportedSimple 0),
  ("simple value 255", refuses (hex "f8ff") .unsupportedSimple 0),
  ("byte string key", refuses (hex "a1410000") .unsupportedKey 1),
  ("keys out of order", refuses (hex "a202000100") .unsortedKeys 3),
  ("text key before integer key", refuses (hex "a26161000100") .unsortedKeys 4),
  ("duplicate key", refuses (hex "a201000100") .duplicateKey 3),
  ("keys out of order inside an array", refuses (hex "81a202000100") .unsortedKeys 4),
  ("invalid UTF-8", refuses (hex "61ff") .invalidUtf8 0),
  ("overlong UTF-8", refuses (hex "62c080") .invalidUtf8 0),
  ("UTF-8 surrogate", refuses (hex "63eda080") .invalidUtf8 0),
  ("nesting at the depth bound", (decode (nestedArrays maxDepth)).toBool),
  ("nesting past the depth bound", refuses (nestedArrays (maxDepth + 1)) .tooDeep maxDepth),
  ("trailing byte", refuses (hex "0000") .trailingBytes 1),
  ("decodePrefix stops after one item",
    match decodePrefix (hex "a10102ffff") 0 with
    | .ok (v, p) => v == .map [(.uint 1, .uint 2)] && p == 3
    | .error _ => false),
  ("decodePrefix starts at its offset",
    match decodePrefix (hex "ff6161") 1 with
    | .ok (v, p) => v == .text "a" && p == 3
    | .error _ => false),
  ("a million-item array decodes", arrayLength millionZeros == some 1000000),
  ("error names are distinct",
    let names := [Reason.truncated, .lengthExceedsInput, .reservedInfo, .indefiniteLength,
      .unexpectedBreak, .nonMinimalHead, .tag, .float, .unsupportedSimple, .unsupportedKey,
      .unsortedKeys, .duplicateKey, .invalidUtf8, .tooDeep, .trailingBytes].map Reason.name
    names.eraseDups.length == names.length)
]

end Tests.Decode
