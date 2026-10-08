/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cbor
public import Leancrypto.Codec.Hex

@[expose] public section

namespace Tests

/-- A malformed literal reads as no bytes, which no fixture expects, so it fails its check rather
than passing silently. -/
def hex (s : String) : ByteArray := (Leancrypto.Codec.Hex.decodeString s).getD .empty

def key (s : String) (h : s.utf8ByteSize < 2 ^ 64 := by decide) : Cbor.Key := .text s h

def decodesTo (input : ByteArray) (v : Cbor.Value) : Bool :=
  match Cbor.decode input with
  | .ok w => w == v
  | .error _ => false

def refuses (input : ByteArray) (reason : Cbor.Reason) (offset : Nat) : Bool :=
  match Cbor.decode input with
  | .ok _ => false
  | .error e => e.reason == reason && e.offset == offset

def bytesEq (a b : ByteArray) : Bool := a.toList == b.toList

end Tests
