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

/-- The entries outside the supported subset, each with the reason it must be refused for and where.
The offset is not always 0: an indefinite-length item nested in a definite one is refused where it
begins. -/
def refusals : List (String × Reason × Nat) := [
  ("c249010000000000000000", .tag, 0),
  ("c349010000000000000000", .tag, 0),
  ("f90000", .float, 0),
  ("f98000", .float, 0),
  ("f93c00", .float, 0),
  ("fb3ff199999999999a", .float, 0),
  ("f93e00", .float, 0),
  ("f97bff", .float, 0),
  ("fa47c35000", .float, 0),
  ("fa7f7fffff", .float, 0),
  ("fb7e37e43c8800759c", .float, 0),
  ("f90001", .float, 0),
  ("f90400", .float, 0),
  ("f9c400", .float, 0),
  ("fbc010666666666666", .float, 0),
  ("f97c00", .float, 0),
  ("f97e00", .float, 0),
  ("f9fc00", .float, 0),
  ("fa7f800000", .float, 0),
  ("fa7fc00000", .float, 0),
  ("faff800000", .float, 0),
  ("fb7ff0000000000000", .float, 0),
  ("fb7ff8000000000000", .float, 0),
  ("fbfff0000000000000", .float, 0),
  ("f7", .unsupportedSimple, 0),
  ("f0", .unsupportedSimple, 0),
  ("f8ff", .unsupportedSimple, 0),
  ("c074323031332d30332d32315432303a30343a30305a", .tag, 0),
  ("c11a514b67b0", .tag, 0),
  ("c1fb41d452d9ec200000", .tag, 0),
  ("d74401020304", .tag, 0),
  ("d818456449455446", .tag, 0),
  ("d82076687474703a2f2f7777772e6578616d706c652e636f6d", .tag, 0),
  ("5f42010243030405ff", .indefiniteLength, 0),
  ("7f657374726561646d696e67ff", .indefiniteLength, 0),
  ("9fff", .indefiniteLength, 0),
  ("9f018202039f0405ffff", .indefiniteLength, 0),
  ("9f01820203820405ff", .indefiniteLength, 0),
  ("83018202039f0405ff", .indefiniteLength, 5),
  ("83019f0203ff820405", .indefiniteLength, 2),
  ("9f0102030405060708090a0b0c0d0e0f101112131415161718181819ff", .indefiniteLength, 0),
  ("bf61610161629f0203ffff", .indefiniteLength, 0),
  ("826161bf61626163ff", .indefiniteLength, 3),
  ("bf6346756ef563416d7421ff", .indefiniteLength, 0)
]

def checks : List (String × Bool) :=
  refusals.map (fun (h, r, o) => (s!"Appendix A refuses {h}", refuses (hex h) r o))
    ++ vectors.map (fun (h, v) => (s!"Appendix A encode {h}", bytesEq v.encode (hex h)))
    ++ vectors.map fun (h, v) => (s!"Appendix A decode {h}", decodesTo (hex h) v)

end Tests.AppendixA
