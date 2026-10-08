/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

/-!
The initial byte and argument that begin every item, always written in the shortest form that holds
the argument. The arithmetic is on `Nat` rather than on bits, because that is what the proofs about
it reason in.
-/

@[expose] public section

namespace Cbor.Head

def unsigned : Nat := 0
def negative : Nat := 1
def byteString : Nat := 2
def textString : Nat := 3
def array : Nat := 4
def map : Nat := 5
def simple : Nat := 7

def falseValue : Nat := 20
def trueValue : Nat := 21
def nullValue : Nat := 22

def initial (major info : Nat) : UInt8 := UInt8.ofNat (major * 32 + info)

/-- The low `count` bytes of `n`, most significant first. -/
def pushBigEndian (out : ByteArray) (n : Nat) : Nat → ByteArray
  | 0 => out
  | count + 1 => pushBigEndian (out.push (UInt8.ofNat (n / 256 ^ count))) n count

/-- Correct only for `n < 2 ^ 64`, which every caller guarantees. -/
def push (out : ByteArray) (major n : Nat) : ByteArray :=
  if n < 24 then out.push (initial major n)
  else if n < 0x100 then pushBigEndian (out.push (initial major 24)) n 1
  else if n < 0x10000 then pushBigEndian (out.push (initial major 25)) n 2
  else if n < 0x100000000 then pushBigEndian (out.push (initial major 26)) n 4
  else pushBigEndian (out.push (initial major 27)) n 8

end Cbor.Head
