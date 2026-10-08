/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cbor
public import Tests.Harness

@[expose] public section

namespace Tests.Encode
open Cbor

/-- `n` arrays, each holding the next, around `null`. -/
def nested : Nat → Value
  | 0 => .null
  | n + 1 => .array [nested n]

def checks : List (String × Bool) := [
  -- RFC 8949's length-first rule would put `""` (60) before 24 (1818); CTAP2 puts the lower major
  -- type first.
  ("major type precedes length",
    bytesEq (Value.map [(key "", .uint 0), (.uint 24, .uint 0)]).encode (hex "a2181800" ++ hex "6000")),
  ("unsigned keys precede negative ones",
    bytesEq (Value.map [(.nint 0, .null), (.uint 1000, .null)]).encode (hex "a21903e8f620f6")),
  ("shorter text keys precede longer ones",
    bytesEq (Value.map [(key "aa", .null), (key "b", .null)]).encode (hex "a26162f6626161f6")),
  ("maps nested in arrays are sorted",
    bytesEq (Value.array [.map [(.uint 2, .null), (.uint 1, .null)]]).encode (hex "81a201f602f6")),
  ("maps nested in maps are sorted",
    bytesEq (Value.map [(.uint 0, .map [(.uint 2, .null), (.uint 1, .null)])]).encode
      (hex "a100a201f602f6")),
  ("distinct keys pass", (Value.map [(.uint 1, .null), (.nint 1, .null)]).distinctKeys),
  ("a duplicate key fails", !(Value.map [(key "a", .null), (.uint 0, .null), (key "a", .null)]).distinctKeys),
  ("a duplicate key in a nested map fails",
    !(Value.array [.map [(.uint 5, .null), (.uint 5, .uint 1)]]).distinctKeys),
  ("nesting at the depth bound is within it", (nested maxDepth).withinDepth),
  ("nesting past the depth bound is not", !(nested (maxDepth + 1)).withinDepth),
  ("a long byte string is cut short in Repr",
    (toString (repr (Value.bytes ⟨Array.replicate 1000 0⟩ (by simp [ByteArray.size])))).length < 200),
  ("ofInt? spans exactly the CBOR integers",
    (Value.ofInt? (-2 ^ 64)).isSome && (Value.ofInt? (2 ^ 64 - 1)).isSome
      && (Value.ofInt? (-2 ^ 64 - 1)).isNone && (Value.ofInt? (2 ^ 64)).isNone),
  ("toInt? inverts ofInt?",
    [-2 ^ 64, -1000, -1, 0, 23, 2 ^ 64 - 1].all fun i => ((Value.ofInt? i).bind (·.toInt?)) == some i)
]

end Tests.Encode
