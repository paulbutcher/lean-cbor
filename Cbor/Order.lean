/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

/-!
The canonical order on map keys, CTAP2's: major type first, then encoded length, then the bytes.

It is defined on encodings rather than on keys so that the decoder, which holds a key only as a
slice of its input, and the encoder, which holds a `Key`, cannot disagree about it.
-/

@[expose] public section

namespace Cbor.Order

def majorType : List UInt8 → UInt8
  | [] => 0
  | b :: _ => b >>> 5

def lex : List UInt8 → List UInt8 → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | a :: as, b :: bs => (compare a b).then (lex as bs)

def compareLists (a b : List UInt8) : Ordering :=
  (compare (majorType a) (majorType b)).then ((compare a.length b.length).then (lex a b))

/-- `.lt` when the key encoded as `a` precedes the one encoded as `b`, and `.eq` exactly when the
two encodings are the same bytes, so one call answers both the ordering and the duplicate
question. -/
def compareEncoded (a b : ByteArray) : Ordering :=
  compareLists a.toList b.toList

end Cbor.Order
