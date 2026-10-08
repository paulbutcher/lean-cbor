/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cbor.Head
public import Cbor.Order
public import Cbor.Value

/-!
`encode` sorts every map before writing it, so a caller gets canonical bytes whatever order it built
the map in. It is `Item.push` applied to `Item.normalise`, kept as two steps so that what the round
trip yields, the normalised value, is a function a theorem can name.
-/

@[expose] public section

namespace Cbor

def Key.push (out : ByteArray) : Key → ByteArray
  | .uint n => Head.push out Head.unsigned n.toNat
  | .nint n => Head.push out Head.negative n.toNat
  | .text s _ => Head.push out Head.textString s.utf8ByteSize ++ s.toUTF8

def Key.encode (k : Key) : ByteArray := k.push .empty

namespace Item

mutual
/-- Writes the item with map entries in the order they are held, sorted or not. -/
def push (out : ByteArray) : Item → ByteArray
  | .uint n => Head.push out Head.unsigned n.toNat
  | .nint n => Head.push out Head.negative n.toNat
  | .bytes b _ => Head.push out Head.byteString b.size ++ b
  | .text s _ => Head.push out Head.textString s.utf8ByteSize ++ s.toUTF8
  | .array xs => pushList (Head.push out Head.array xs.length) xs
  | .map es => pushEntries (Head.push out Head.map es.length) es
  | .bool false => Head.push out Head.simple Head.falseValue
  | .bool true => Head.push out Head.simple Head.trueValue
  | .null => Head.push out Head.simple Head.nullValue

def pushList (out : ByteArray) : List Item → ByteArray
  | [] => out
  | x :: xs => pushList (push out x) xs

def pushEntries (out : ByteArray) : List (Key × Item) → ByteArray
  | [] => out
  | (k, x) :: es => pushEntries (push (k.push out) x) es
end

def entryPrecedes (a b : Key × Item) : Bool :=
  Order.compareEncoded a.1.encode b.1.encode != .gt

mutual
/-- Sorts every map's entries into canonical order, at every depth. The sort is stable, so entries
with equal keys keep their relative order, though such a map has no canonical form. -/
def normalise : Item → Item
  | .array xs => .array (normaliseList xs)
  | .map es => .map ((normaliseEntries es).mergeSort entryPrecedes)
  | x => x

def normaliseList : List Item → List Item
  | [] => []
  | x :: xs => x.normalise :: normaliseList xs

def normaliseEntries : List (Key × Item) → List (Key × Item)
  | [] => []
  | (k, x) :: es => (k, x.normalise) :: normaliseEntries es
end

def encode (x : Item) : ByteArray := x.normalise.push .empty

def strictlyIncreasing : List ByteArray → Bool
  | a :: b :: rest => Order.compareEncoded a b == .lt && strictlyIncreasing (b :: rest)
  | _ => true

/-- Sorts the entries as `normalise` does, so that a map passing this is one `normalise` leaves
strictly increasing. -/
def keysDistinct (es : List (Key × Item)) : Bool :=
  strictlyIncreasing ((es.mergeSort entryPrecedes).map (·.1.encode))

mutual
def distinctKeys : Item → Bool
  | .array xs => distinctKeysList xs
  | .map es => keysDistinct es && distinctKeysEntries es
  | _ => true

def distinctKeysList : List Item → Bool
  | [] => true
  | x :: xs => x.distinctKeys && distinctKeysList xs

def distinctKeysEntries : List (Key × Item) → Bool
  | [] => true
  | (_, x) :: es => x.distinctKeys && distinctKeysEntries es
end

end Item

namespace Value

def encode (v : Value) : ByteArray := v.item.encode

/-- No map at any depth holds the same key twice. `encode` on a value failing this produces bytes
`decode` refuses. -/
def distinctKeys (v : Value) : Bool := v.item.distinctKeys

end Value

end Cbor
