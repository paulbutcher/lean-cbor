/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cbor
public import Tests.Harness

/-!
RFC 8949 Appendix A, transcribed from the RFC: the entries inside the supported subset, each with
the value it denotes. `-18446744073709551616` is the most negative integer CBOR has, and the one
entry here that reaches the top of `nint`.
-/

@[expose] public section

namespace Tests.AppendixA
open Cbor

def vectors : List (String × Value) := [
  ("00", .uint 0),
  ("01", .uint 1),
  ("0a", .uint 10),
  ("17", .uint 23),
  ("1818", .uint 24),
  ("1819", .uint 25),
  ("1864", .uint 100),
  ("1903e8", .uint 1000),
  ("1a000f4240", .uint 1000000),
  ("1b000000e8d4a51000", .uint 1000000000000),
  ("1bffffffffffffffff", .uint 18446744073709551615),
  ("3bffffffffffffffff", .nint 18446744073709551615),
  ("20", .nint 0),
  ("29", .nint 9),
  ("3863", .nint 99),
  ("3903e7", .nint 999),
  ("f4", .bool false),
  ("f5", .bool true),
  ("f6", .null),
  ("40", .bytes ByteArray.empty),
  ("4401020304", .bytes ⟨#[1, 2, 3, 4]⟩),
  ("60", .text ""),
  ("6161", .text "a"),
  ("6449455446", .text "IETF"),
  ("62225c", .text "\"\\"),
  ("62c3bc", .text "ü"),
  ("63e6b0b4", .text "水"),
  ("64f0908591", .text "𐅑"),
  ("80", .array []),
  ("83010203", .array [.uint 1, .uint 2, .uint 3]),
  ("8301820203820405",
    .array [.uint 1, .array [.uint 2, .uint 3], .array [.uint 4, .uint 5]]),
  ("98190102030405060708090a0b0c0d0e0f101112131415161718181819",
    .array ((List.range 25).map fun i => .uint (i + 1).toUInt64)),
  ("a0", .map []),
  ("a201020304", .map [(.uint 1, .uint 2), (.uint 3, .uint 4)]),
  ("a26161016162820203", .map [(key "a", .uint 1), (key "b", .array [.uint 2, .uint 3])]),
  ("826161a161626163", .array [.text "a", .map [(key "b", .text "c")]]),
  ("a56161614161626142616361436164614461656145",
    .map [(key "a", .text "A"), (key "b", .text "B"), (key "c", .text "C"), (key "d", .text "D"),
      (key "e", .text "E")])
]

def checks : List (String × Bool) :=
  vectors.map fun (h, v) => (s!"Appendix A encode {h}", bytesEq v.encode (hex h))

end Tests.AppendixA
