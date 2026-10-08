/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

/-!
The initial byte and argument that begin every item, always written in the shortest form that holds
the argument.
-/

@[expose] public section

namespace Cbor.Head

def unsigned : UInt8 := 0
def negative : UInt8 := 1
def byteString : UInt8 := 2
def textString : UInt8 := 3
def array : UInt8 := 4
def map : UInt8 := 5
def simple : UInt8 := 7

def falseValue : UInt8 := 20
def trueValue : UInt8 := 21
def nullValue : UInt8 := 22

/-- The low `count` bytes of `n`, most significant first. -/
def pushBigEndian (out : ByteArray) (n : UInt64) : Nat → ByteArray
  | 0 => out
  | count + 1 => pushBigEndian (out.push (n >>> (8 * count).toUInt64).toUInt8) n count

def push (out : ByteArray) (major : UInt8) (n : UInt64) : ByteArray :=
  let initial := major <<< 5
  if n < 24 then out.push (initial ||| n.toUInt8)
  else if n < 0x100 then pushBigEndian (out.push (initial ||| 24)) n 1
  else if n < 0x10000 then pushBigEndian (out.push (initial ||| 25)) n 2
  else if n < 0x100000000 then pushBigEndian (out.push (initial ||| 26)) n 4
  else pushBigEndian (out.push (initial ||| 27)) n 8

end Cbor.Head
