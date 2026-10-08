/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

/-!
The data model. `Item` is the tree; `Value` is an `Item` whose every length fits a CBOR head.

String lengths are bounded in the constructors. Array and map counts cannot be, because the kernel
refuses a proof about a list inside the constructor that nests it, so `Value` carries a proof that
`Item.bounded` holds instead.
-/

@[expose] public section

namespace Cbor

/-- Map keys are limited to integers and text strings. For these, two keys are equal exactly when
their encodings are, which is what lets a duplicate be detected by comparing encodings. -/
inductive Key where
  | uint (n : UInt64)
  /-- The integer `-1 - n`. -/
  | nint (n : UInt64)
  | text (s : String) (h : s.utf8ByteSize < 2 ^ 64)
deriving DecidableEq, Inhabited

inductive Item where
  | uint (n : UInt64)
  /-- The integer `-1 - n`. -/
  | nint (n : UInt64)
  | bytes (b : ByteArray) (h : b.size < 2 ^ 64)
  | text (s : String) (h : s.utf8ByteSize < 2 ^ 64)
  | array (xs : List Item)
  | map (es : List (Key × Item))
  | bool (b : Bool)
  | null
deriving Inhabited

namespace Item

mutual
def decEq : (a b : Item) → Decidable (a = b)
  | .uint m, .uint n =>
    if h : m = n then isTrue (h ▸ rfl) else isFalse (by intro e; cases e; exact h rfl)
  | .nint m, .nint n =>
    if h : m = n then isTrue (h ▸ rfl) else isFalse (by intro e; cases e; exact h rfl)
  | .bytes a _, .bytes b _ =>
    if h : a = b then isTrue (by subst h; rfl) else isFalse (by intro e; cases e; exact h rfl)
  | .text a _, .text b _ =>
    if h : a = b then isTrue (by subst h; rfl) else isFalse (by intro e; cases e; exact h rfl)
  | .array xs, .array ys =>
    match decEqList xs ys with
    | isTrue h => isTrue (h ▸ rfl)
    | isFalse h => isFalse (by intro e; cases e; exact h rfl)
  | .map xs, .map ys =>
    match decEqEntries xs ys with
    | isTrue h => isTrue (h ▸ rfl)
    | isFalse h => isFalse (by intro e; cases e; exact h rfl)
  | .bool a, .bool b =>
    if h : a = b then isTrue (h ▸ rfl) else isFalse (by intro e; cases e; exact h rfl)
  | .null, .null => isTrue rfl
  | .uint _, .nint _ | .uint _, .bytes _ _ | .uint _, .text _ _ | .uint _, .array _
  | .uint _, .map _ | .uint _, .bool _ | .uint _, .null
  | .nint _, .uint _ | .nint _, .bytes _ _ | .nint _, .text _ _ | .nint _, .array _
  | .nint _, .map _ | .nint _, .bool _ | .nint _, .null
  | .bytes _ _, .uint _ | .bytes _ _, .nint _ | .bytes _ _, .text _ _ | .bytes _ _, .array _
  | .bytes _ _, .map _ | .bytes _ _, .bool _ | .bytes _ _, .null
  | .text _ _, .uint _ | .text _ _, .nint _ | .text _ _, .bytes _ _ | .text _ _, .array _
  | .text _ _, .map _ | .text _ _, .bool _ | .text _ _, .null
  | .array _, .uint _ | .array _, .nint _ | .array _, .bytes _ _ | .array _, .text _ _
  | .array _, .map _ | .array _, .bool _ | .array _, .null
  | .map _, .uint _ | .map _, .nint _ | .map _, .bytes _ _ | .map _, .text _ _
  | .map _, .array _ | .map _, .bool _ | .map _, .null
  | .bool _, .uint _ | .bool _, .nint _ | .bool _, .bytes _ _ | .bool _, .text _ _
  | .bool _, .array _ | .bool _, .map _ | .bool _, .null
  | .null, .uint _ | .null, .nint _ | .null, .bytes _ _ | .null, .text _ _
  | .null, .array _ | .null, .map _ | .null, .bool _ => isFalse (by intro e; cases e)

def decEqList : (a b : List Item) → Decidable (a = b)
  | [], [] => isTrue rfl
  | [], _ :: _ | _ :: _, [] => isFalse (by intro e; cases e)
  | x :: xs, y :: ys =>
    match decEq x y, decEqList xs ys with
    | isTrue h, isTrue h' => isTrue (h ▸ h' ▸ rfl)
    | isFalse h, _ => isFalse (by intro e; cases e; exact h rfl)
    | _, isFalse h => isFalse (by intro e; cases e; exact h rfl)

def decEqEntries : (a b : List (Key × Item)) → Decidable (a = b)
  | [], [] => isTrue rfl
  | [], _ :: _ | _ :: _, [] => isFalse (by intro e; cases e)
  | (k, x) :: xs, (l, y) :: ys =>
    if hk : k = l then
      match decEq x y, decEqEntries xs ys with
      | isTrue h, isTrue h' => isTrue (hk ▸ h ▸ h' ▸ rfl)
      | isFalse h, _ => isFalse (by intro e; cases e; exact h rfl)
      | _, isFalse h => isFalse (by intro e; cases e; exact h rfl)
    else isFalse (by intro e; cases e; exact hk rfl)
end

instance : DecidableEq Item := decEq

mutual
def bounded : Item → Bool
  | .array xs => decide (xs.length < 2 ^ 64) && boundedList xs
  | .map es => decide (es.length < 2 ^ 64) && boundedEntries es
  | _ => true

def boundedList : List Item → Bool
  | [] => true
  | x :: xs => x.bounded && boundedList xs

def boundedEntries : List (Key × Item) → Bool
  | [] => true
  | (_, x) :: es => x.bounded && boundedEntries es
end

/--
Checking a list of items for bounded lengths is the same as asking every item in it. This turns the
mutual recursion into a statement about `List.all`, which `simp` can take apart, and it is how a
proof that an array is bounded yields a proof for each of its elements.

`boundedList xs` answers `true` when every item of `xs` is `bounded`, and `xs.all bounded` answers
`true` under the same condition stated with the library function, so the equation says the two
agree on every list.
-/
theorem boundedList_eq_all (xs : List Item) : boundedList xs = xs.all bounded := by
  induction xs with
  | nil => simp [boundedList]
  | cons x xs ih => simp [boundedList, ih]

/--
Checking a map's entries for bounded lengths is the same as asking every entry's value. As with
lists, this is what lets a proof that a map is bounded yield a proof for each of its values; keys
need no check, because a text key carries its own bound.

`boundedEntries es` answers `true` when the value of every entry of `es` is `bounded`, and the right
side asks the same of each entry's second component, so the equation says the two agree on every
list of entries.
-/
theorem boundedEntries_eq_all (es : List (Key × Item)) :
    boundedEntries es = es.all (·.2.bounded) := by
  induction es with
  | nil => simp [boundedEntries]
  | cons e es ih => obtain ⟨_, _⟩ := e; simp [boundedEntries, ih]

mutual
/-- Arrays and maps nest at most `depth` deep. It stops descending at the bound, so it is safe on
the over-deep values it exists to catch. -/
def withinDepth : Nat → Item → Bool
  | 0, .array _ | 0, .map _ => false
  | d + 1, .array xs => withinDepthList d xs
  | d + 1, .map es => withinDepthEntries d es
  | _, _ => true

def withinDepthList (depth : Nat) : List Item → Bool
  | [] => true
  | x :: xs => x.withinDepth depth && withinDepthList depth xs

def withinDepthEntries (depth : Nat) : List (Key × Item) → Bool
  | [] => true
  | (_, x) :: es => x.withinDepth depth && withinDepthEntries depth es
end

end Item

/-- The decoder refuses nesting deeper than this. It is fixed because the traversals recurse on the
stack, so raising it would trade the guarantee against hostile input for depth no target consumer
needs. -/
def maxDepth : Nat := 1024

structure Value where
  item : Item
  isBounded : item.bounded = true
deriving DecidableEq

namespace Key

def text? (s : String) : Option Key :=
  if h : s.utf8ByteSize < 2 ^ 64 then some (.text s h) else none

/-- `none` outside the range CBOR integers span, `-2^64` to `2^64 - 1`. -/
def ofInt? (i : Int) : Option Key :=
  if 0 ≤ i ∧ i < 2 ^ 64 then some (.uint i.toNat.toUInt64)
  else if -2 ^ 64 ≤ i ∧ i < 0 then some (.nint (-1 - i).toNat.toUInt64)
  else none

def toInt? : Key → Option Int
  | .uint n => some n.toNat
  | .nint n => some (-1 - n.toNat)
  | .text _ _ => none

def toItem : Key → Item
  | .uint n => .uint n
  | .nint n => .nint n
  | .text s h => .text s h

end Key

/--
The items underlying a list of `Value`s are bounded throughout. This is what lets `Value.array`
build a bounded item from values without checking them again.

`xs.map (·.item)` takes the item out of each value, and `Item.boundedList` answers `true` when every
one of those is bounded; each is, by the proof its `Value` carries, so the equation holds for every
list of values.
-/
private theorem boundedList_map (xs : List Value) : Item.boundedList (xs.map (·.item)) = true := by
  simp [Item.boundedList_eq_all, Value.isBounded]

/--
The items underlying a list of map entries whose values are `Value`s are bounded throughout. This is
what lets `Value.map` build a bounded item from entries without checking them again.

The map replaces each entry's value with its item and keeps the key, and `Item.boundedEntries`
answers `true` when every such item is bounded; each is, by the proof its `Value` carries, so the
equation holds for every list of entries.
-/
private theorem boundedEntries_map (es : List (Key × Value)) :
    Item.boundedEntries (es.map fun e => (e.1, e.2.item)) = true := by
  simp [Item.boundedEntries_eq_all, Value.isBounded]

namespace Value

def uint (n : UInt64) : Value := ⟨.uint n, rfl⟩

/-- The integer `-1 - n`. -/
def nint (n : UInt64) : Value := ⟨.nint n, rfl⟩

def bool (b : Bool) : Value := ⟨.bool b, rfl⟩

def null : Value := ⟨.null, rfl⟩

def bytes (b : ByteArray) (h : b.size < 2 ^ 64 := by decide) : Value := ⟨.bytes b h, rfl⟩

def text (s : String) (h : s.utf8ByteSize < 2 ^ 64 := by decide) : Value := ⟨.text s h, rfl⟩

def array (xs : List Value) (h : xs.length < 2 ^ 64 := by first | decide | simp) : Value :=
  ⟨.array (xs.map (·.item)), by simp [Item.bounded, h, boundedList_map]⟩

def map (es : List (Key × Value)) (h : es.length < 2 ^ 64 := by first | decide | simp) : Value :=
  ⟨.map (es.map fun e => (e.1, e.2.item)), by simp [Item.bounded, h, boundedEntries_map]⟩

def bytes? (b : ByteArray) : Option Value :=
  if h : b.size < 2 ^ 64 then some (bytes b h) else none

def text? (s : String) : Option Value :=
  if h : s.utf8ByteSize < 2 ^ 64 then some (text s h) else none

def array? (xs : List Value) : Option Value :=
  if h : xs.length < 2 ^ 64 then some (array xs h) else none

def map? (es : List (Key × Value)) : Option Value :=
  if h : es.length < 2 ^ 64 then some (map es h) else none

/-- `none` outside the range CBOR integers span, `-2^64` to `2^64 - 1`. -/
def ofInt? (i : Int) : Option Value :=
  (Key.ofInt? i).map fun k => ⟨k.toItem, by cases k <;> rfl⟩

def ofKey (k : Key) : Value := ⟨k.toItem, by cases k <;> rfl⟩

def toInt? (v : Value) : Option Int :=
  match v.item with
  | .uint n => some n.toNat
  | .nint n => some (-1 - n.toNat)
  | _ => none

def withinDepth (v : Value) : Bool := v.item.withinDepth maxDepth

end Value

namespace Item

def hexDigit (n : UInt8) : Char :=
  if n < 10 then Char.ofNat (48 + n.toNat) else Char.ofNat (87 + n.toNat)

/-- Bytes shown before a byte string is cut short, so that a payload reaching a log does not fill
it. -/
def reprByteLimit : Nat := 32

def formatBytes (b : ByteArray) : Std.Format :=
  let shown := b.toList.take reprByteLimit
  let hex := String.ofList (shown.flatMap fun (x : UInt8) => [hexDigit (x >>> 4), hexDigit (x &&& 15)])
  if b.size ≤ reprByteLimit then s!"h'{hex}'" else s!"h'{hex}…' ({b.size} bytes)"

def formatKey : Key → Std.Format
  | .uint n => toString n
  | .nint n => s!"-{n.toNat + 1}"
  | .text s _ => s.quote

mutual
def format : Item → Std.Format
  | .uint n => toString n
  | .nint n => s!"-{n.toNat + 1}"
  | .bytes b _ => formatBytes b
  | .text s _ => s.quote
  | .array xs => .bracket "[" (.joinSep (formatList xs) ("," ++ .line)) "]"
  | .map es => .bracket "{" (.joinSep (formatEntries es) ("," ++ .line)) "}"
  | .bool b => toString b
  | .null => "null"

def formatList : List Item → List Std.Format
  | [] => []
  | x :: xs => x.format :: formatList xs

def formatEntries : List (Key × Item) → List Std.Format
  | [] => []
  | (k, x) :: es => (formatKey k ++ ": " ++ x.format) :: formatEntries es
end

instance : Repr Item where
  reprPrec x _ := x.format

end Item

instance : Repr Value where
  reprPrec v _ := v.item.format

/-- One layer of a `Value`, for reading it without reaching into `Item`. -/
inductive View where
  | uint (n : UInt64)
  /-- The integer `-1 - n`. -/
  | nint (n : UInt64)
  | bytes (b : ByteArray)
  | text (s : String)
  | array (xs : List Value)
  | map (es : List (Key × Value))
  | bool (b : Bool)
  | null

def Value.view : Value → View
  | ⟨.uint n, _⟩ => .uint n
  | ⟨.nint n, _⟩ => .nint n
  | ⟨.bytes b _, _⟩ => .bytes b
  | ⟨.text s _, _⟩ => .text s
  | ⟨.array xs, h⟩ =>
    .array <| xs.attach.map fun ⟨x, hx⟩ =>
      ⟨x, by
        simp only [Item.bounded, Bool.and_eq_true, Item.boundedList_eq_all, List.all_eq_true] at h
        exact h.2 x hx⟩
  | ⟨.map es, h⟩ =>
    .map <| es.attach.map fun ⟨e, he⟩ =>
      (e.1, ⟨e.2, by
        simp only [Item.bounded, Bool.and_eq_true, Item.boundedEntries_eq_all,
          List.all_eq_true] at h
        exact h.2 e he⟩)
  | ⟨.bool b, _⟩ => .bool b
  | ⟨.null, _⟩ => .null

end Cbor
