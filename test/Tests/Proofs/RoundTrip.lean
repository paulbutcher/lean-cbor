/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Tests.Proofs.Read

@[expose] public section

namespace Tests.Proofs
open Cbor

mutual
/-- Every map's keys, as held, have strictly increasing encodings. -/
def sorted : Item → Bool
  | .array xs => sortedList xs
  | .map es => Item.strictlyIncreasing (es.map (·.1.encode)) && sortedEntries es
  | _ => true

def sortedList : List Item → Bool
  | [] => true
  | x :: xs => sorted x && sortedList xs

def sortedEntries : List (Key × Item) → Bool
  | [] => true
  | (_, x) :: es => sorted x && sortedEntries es
end

/--
The encodings of `false`, `true` and `null` are read back as those values. They are the three simple
values the library supports, and the only heads read without an argument.

`v` is the additional information and `val` the value it denotes, for each of the three pairs; with
the initial byte for major type 7 and `v` at `pos`, `Decode.readHead` returns `val` as a simple
head, ending one byte later.
-/
theorem readHead_simple {v : Nat} {val : Value}
    (hv : (v = 20 ∧ val = .bool false) ∨ (v = 21 ∧ val = .bool true) ∨
      (v = 22 ∧ val = .null))
    {input : ByteArray} {pos : Nat} (h : At input pos [Head.initial 7 v]) :
    ∃ hp, Decode.readHead input pos = .ok (.simple val, ⟨pos + 1, hp⟩) := by
  obtain ⟨hp, hx⟩ := h.getElem
  have hv' : input[pos].toNat = 7 * 32 + v := by
    rw [hx]; exact initial_toNat (by omega) (by omega)
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  unfold Decode.readHead
  rw [dite_eq_left hp]
  have h1 : (7 * 32 + v) / 32 = 7 := by omega
  have h2 : (7 * 32 + v) % 32 = v := by omega
  simp only [hv', h1, h2]
  rcases hv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl

/--
Every item's encoding is at least one byte. The decoder refuses an array or map whose declared count
exceeds the bytes remaining, and that refusal is only sound because no item is shorter than a byte.

`(x.push .empty).size` is the length of `x` written alone, and the inequality says it is never zero.
-/
theorem push_size_pos (x : Item) : 1 ≤ (x.push .empty).size := by
  rw [size_eq_length]
  cases x with
  | array xs => rw [Item.push, pushList_data, head_data]; unfold Head.push; repeat' split
                all_goals simp [pushBigEndian_data]
  | map es => rw [Item.push, pushEntries_data, head_data]; unfold Head.push; repeat' split
              all_goals simp [pushBigEndian_data]
  | bytes | text => simp only [Item.push, data_append]; rw [head_data]; unfold Head.push
                    repeat' split
                    all_goals simp [pushBigEndian_data]
  | bool b => cases b <;> simp [Item.push, Head.push, Head.falseValue, Head.trueValue]
  | _ => simp only [Item.push]; rw [head_data]; unfold Head.push; repeat' split
         all_goals simp [pushBigEndian_data]

/--
A list of items takes at least as many bytes as it has items. It is what shows a genuine array's
count passes the decoder's check against the bytes remaining.

`xs.length` is the count the head declares and the right side is the length of the elements'
encoding, which the inequality says is no smaller.
-/
theorem length_le_pushList (xs : List Item) :
    xs.length ≤ (Item.pushList .empty xs).data.toList.length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [Item.pushList]
    rw [pushList_data]
    have := push_size_pos x
    rw [size_eq_length] at this
    simp only [List.length_cons, List.length_append]
    omega

/--
A list of map entries takes at least as many bytes as it has entries. It is what shows a genuine
map's count passes the decoder's check against the bytes remaining.

`es.length` is the count the head declares and the right side is the length of the entries'
encoding, which the inequality says is no smaller.
-/
theorem length_le_pushEntries (es : List (Key × Item)) :
    es.length ≤ (Item.pushEntries .empty es).data.toList.length := by
  induction es with
  | nil => simp
  | cons e es ih =>
    obtain ⟨k, x⟩ := e
    simp only [Item.pushEntries]
    rw [pushEntries_data, push_data]
    have := push_size_pos x
    rw [size_eq_length] at this
    simp only [List.length_cons, List.length_append]
    omega

/--
A strictly increasing list of encodings stays strictly increasing without its first element. It is
what carries the ordering hypothesis from one map entry to the next.

`Item.strictlyIncreasing (a :: l)` answers `true` when each encoding precedes the next; the
conclusion asks the same of `l`.
-/
theorem strictlyIncreasing_tail {a : ByteArray} {l : List ByteArray}
    (h : Item.strictlyIncreasing (a :: l) = true) : Item.strictlyIncreasing l = true := by
  cases l with
  | nil => rfl
  | cons b l => simp [Item.strictlyIncreasing] at h; exact h.2

/--
The decoder's order check passes a key that follows its predecessor in a strictly increasing chain.
It is the step at which a canonical map's keys are shown to satisfy the inline check of CBOR-6.3.

`previous.toList` is the encoding of the key before, if there was one; the hypothesis says it, then
`k`, then the rest strictly increase, and the conclusion says `Decode.checkOrder` accepts `k`. The
position only labels a refusal, so it is free.
-/
theorem checkOrder_ok {previous : Option ByteArray} {k : ByteArray} {l : List ByteArray}
    (h : Item.strictlyIncreasing (previous.toList ++ k :: l) = true) (pos : Nat) :
    Decode.checkOrder previous k pos = .ok () := by
  cases previous with
  | none => rfl
  | some p =>
    simp [Item.strictlyIncreasing] at h
    simp [Decode.checkOrder, h.1]

/--
Byte-string values are equal when their bytes are, whatever proofs of their bound they carry. The
decoder builds its value around a slice of the input, and this equates it with the one the encoder
was given.

`Value.bytes a ha` and `Value.bytes b hb` are the two values, and `a = b` is all the conclusion
needs.
-/
theorem bytes_congr {a b : ByteArray} {ha : a.size < 2 ^ 64} {hb : b.size < 2 ^ 64} (h : a = b) :
    Value.bytes a ha = Value.bytes b hb := by
  subst h; rfl

/--
An array's encoding is its head followed by its elements' encodings. It names the shape the array
case of the round trip takes apart.

The left side is the bytes of `Item.array xs` written alone; the right side is a major type 4 head
with the count `xs.length`, then the elements written alone.
-/
theorem item_data_array (xs : List Item) :
    ((Item.array xs).push .empty).data.toList =
      (Head.push .empty 4 xs.length).data.toList ++ (Item.pushList .empty xs).data.toList := by
  simp only [Item.push, Head.array]; rw [pushList_data]

/--
A map's encoding is its head followed by its entries' encodings. It names the shape the map case of
the round trip takes apart.

The left side is the bytes of `Item.map es` written alone; the right side is a major type 5 head
with the count `es.length`, then the entries written alone, in the order held.
-/
theorem item_data_map (es : List (Key × Item)) :
    ((Item.map es).push .empty).data.toList =
      (Head.push .empty 5 es.length).data.toList ++ (Item.pushEntries .empty es).data.toList := by
  simp only [Item.push, Head.map]; rw [pushEntries_data]

mutual
/--
The decoder reads back any item it could have produced, from any position, and stops just past it.
This is the round trip at the level of the decoder's own recursion; `decode_encode` is its use at
the start of an otherwise empty input.

`x.bounded`, `x.withinDepth d` and `sorted x` say every length fits a head, nesting is within `d`,
and every map's keys strictly increase as held, which are the conditions under which the decoder
accepts an encoding as written. With `x` written alone appearing at `pos`, `Decode.item` with depth
`d` succeeds with a value whose item is `x`, ending at `pos` plus the encoding's size. The depth
hypothesis does not make this vacuous: `withinDepth d` admits every item of nesting up to `d`, and
the decoder is called with exactly that depth.
-/
theorem item_ok : (x : Item) → ∀ (d : Nat) (input : ByteArray) (pos : Nat),
    x.bounded = true → x.withinDepth d = true → sorted x = true →
    At input pos (x.push .empty).data.toList →
    ∃ v hp, Decode.item input d pos = .ok (v, ⟨pos + (x.push .empty).size, hp⟩) ∧ v.item = x
  | .uint n, d, input, pos, _, _, _, h => by
    obtain ⟨hp, hr⟩ := readHead_push (major := 0) (by omega) n.toNat_lt
      (by simpa [Item.push, Head.unsigned] using h)
    refine ⟨.uint n, by simpa [Item.push, Head.unsigned] using hp, ?_, rfl⟩
    unfold Decode.item
    rw [hr]
    simp [Decode.Head.ofMajor, Value.uint, Item.push, Head.unsigned]
  | .nint n, d, input, pos, _, _, _, h => by
    obtain ⟨hp, hr⟩ := readHead_push (major := 1) (by omega) n.toNat_lt
      (by simpa [Item.push, Head.negative] using h)
    refine ⟨.nint n, by simpa [Item.push, Head.negative] using hp, ?_, rfl⟩
    unfold Decode.item
    rw [hr]
    simp [Decode.Head.ofMajor, Value.nint, Item.push, Head.negative]
  | .bool false, d, input, pos, _, _, _, h => by
    obtain ⟨hp, hr⟩ := readHead_simple (v := 20) (val := .bool false) (by simp)
      (by simpa [Item.push, Head.push, Head.simple, Head.falseValue] using h)
    refine ⟨.bool false, by simpa [Item.push, Head.push, Head.simple, Head.falseValue] using hp,
      ?_, rfl⟩
    unfold Decode.item
    rw [hr]
    simp [Item.push, Head.push, Head.simple, Head.falseValue]
  | .bool true, d, input, pos, _, _, _, h => by
    obtain ⟨hp, hr⟩ := readHead_simple (v := 21) (val := .bool true) (by simp)
      (by simpa [Item.push, Head.push, Head.simple, Head.trueValue] using h)
    refine ⟨.bool true, by simpa [Item.push, Head.push, Head.simple, Head.trueValue] using hp,
      ?_, rfl⟩
    unfold Decode.item
    rw [hr]
    simp [Item.push, Head.push, Head.simple, Head.trueValue]
  | .null, d, input, pos, _, _, _, h => by
    obtain ⟨hp, hr⟩ := readHead_simple (v := 22) (val := .null) (by simp)
      (by simpa [Item.push, Head.push, Head.simple, Head.nullValue] using h)
    refine ⟨.null, by simpa [Item.push, Head.push, Head.simple, Head.nullValue] using hp,
      ?_, rfl⟩
    unfold Decode.item
    rw [hr]
    simp [Item.push, Head.push, Head.simple, Head.nullValue]
  | .bytes b hb, d, input, pos, _, _, _, h => by
    have h' : At input pos ((Head.push .empty 2 b.size).data.toList ++ b.data.toList) := by
      simpa [Item.push, Head.byteString, data_append] using h
    obtain ⟨hp, hr⟩ := readHead_push (major := 2) (by omega) hb h'.left
    have hat := h'.right
    rw [← size_eq_length] at hat
    obtain ⟨hb', hq, hs⟩ := readSlice_ok (pos := pos) (hp := hp.1) (n := UInt64.ofNat b.size)
      hat
      (by rw [UInt64.toNat_ofNat_of_lt' hb, size_eq_length]) hp.2
    have hext : input.extract (pos + (Head.push .empty 2 b.size).size)
        (pos + (Head.push .empty 2 b.size).size + (UInt64.ofNat b.size).toNat) = b := by
      have hx := hat.extract
      rw [← size_eq_length] at hx
      apply bytes_ext
      rw [UInt64.toNat_ofNat_of_lt' hb, hx]
    have hend : pos + (Head.push .empty 2 b.size).size + (UInt64.ofNat b.size).toNat =
        pos + ((Item.bytes b hb).push .empty).size := by
      simp [Item.push, Head.byteString, ByteArray.size_append, UInt64.toNat_ofNat_of_lt' hb,
        Nat.add_assoc]
    refine ⟨.bytes b hb, hend ▸ hq, ?_, rfl⟩
    unfold Decode.item
    rw [hr]
    simp only [Decode.Head.ofMajor]
    simp only [show (2 == 0) = false from rfl, show (2 == 1) = false from rfl,
      show (2 == 2) = true from rfl, Bool.false_eq_true, ↓reduceIte]
    rw [hs]
    simp only [Except.ok.injEq, Prod.mk.injEq, Subtype.mk.injEq]
    refine ⟨?_, hend⟩
    exact bytes_congr hext
  | .text s hs, d, input, pos, _, _, _, h => by
    have h' : At input pos ((Head.push .empty 3 s.utf8ByteSize).data.toList ++
        s.toUTF8.data.toList) := by
      simpa [Item.push, Head.textString, data_append] using h
    obtain ⟨hp, hr⟩ := readHead_push (major := 3) (by omega) hs h'.left
    have hat := h'.right
    rw [← size_eq_length] at hat
    obtain ⟨_, hq, ht⟩ := readText_ok (pos := pos) (hp := hp.1)
      (n := UInt64.ofNat s.utf8ByteSize)
      hat (UInt64.toNat_ofNat_of_lt' hs) hp.2
    have hend : pos + (Head.push .empty 3 s.utf8ByteSize).size +
        (UInt64.ofNat s.utf8ByteSize).toNat =
        pos + ((Item.text s hs).push .empty).size := by
      simp [Item.push, Head.textString, ByteArray.size_append, UInt64.toNat_ofNat_of_lt' hs,
        Nat.add_assoc]
    refine ⟨.text s hs, hend ▸ hq, ?_, rfl⟩
    unfold Decode.item
    rw [hr]
    simp only [Decode.Head.ofMajor]
    simp only [show (3 == 0) = false from rfl, show (3 == 1) = false from rfl,
      show (3 == 2) = false from rfl, show (3 == 3) = true from rfl, Bool.false_eq_true,
      ↓reduceIte]
    rw [ht]
    simp only [Except.ok.injEq, Prod.mk.injEq, Subtype.mk.injEq]
    constructor <;> first | trivial | exact hend
  | .array xs, d, input, pos, hb, hd, hsrt, h => by
    have ⟨hlen, hbl⟩ : xs.length < 2 ^ 64 ∧ Item.boundedList xs = true := by
      simpa [Item.bounded] using hb
    cases d with
    | zero => simp [Item.withinDepth] at hd
    | succ d =>
    have hd' : Item.withinDepthList d xs = true := by simpa [Item.withinDepth] using hd
    have hs' : sortedList xs = true := by simpa [sorted] using hsrt
    rw [item_data_array] at h
    obtain ⟨hp, hr⟩ := readHead_push (major := 4) (by omega) hlen h.left
    have hat := h.right
    rw [← size_eq_length] at hat
    have hle := hat.le_size' hp.2
    have hcount := length_le_pushList xs
    obtain ⟨ys, hys, hq, hitems, hmap⟩ :=
      items_ok xs d input _ _ (UInt64.ofNat xs.length).toNat (Nat.le_refl _) hp.2 []
        (by simp [UInt64.toNat_ofNat_of_lt' hlen]) hbl hd' hs' hat
    have hend : pos + (Head.push .empty 4 xs.length).size + (Item.pushList .empty xs).size =
        pos + ((Item.array xs).push .empty).size := by
      rw [size_eq_length ((Item.array xs).push .empty), item_data_array, List.length_append,
        size_eq_length (Head.push .empty 4 xs.length), size_eq_length (Item.pushList .empty xs)]
      omega
    have hys' : ys.length < 2 ^ 64 := by rw [hys]; exact UInt64.toNat_lt _
    have hq' : pos < pos + ((Item.array xs).push .empty).size ∧
        pos + ((Item.array xs).push .empty).size ≤ input.size := by
      rw [← hend]; exact ⟨by omega, hq.2⟩
    refine ⟨Value.array ys hys', hq', ?_, by simp [Value.array, hmap]⟩
    unfold Decode.item
    rw [hr]
    simp only [Decode.Head.ofMajor]
    simp only [show (4 == 0) = false from rfl, show (4 == 1) = false from rfl,
      show (4 == 2) = false from rfl, show (4 == 3) = false from rfl,
      show (4 == 4) = true from rfl, Bool.false_eq_true, ↓reduceIte]
    simp only [UInt64.toNat_ofNat_of_lt' hlen]
    rw [ite_eq_left (by have := size_eq_length (Item.pushList .empty xs); omega)]
    rw [hitems]
    simp only [Except.ok.injEq, Prod.mk.injEq, Subtype.mk.injEq]
    constructor <;> first | trivial | exact hend
  | .map es, d, input, pos, hb, hd, hsrt, h => by
    have ⟨hlen, hbl⟩ : es.length < 2 ^ 64 ∧ Item.boundedEntries es = true := by
      simpa [Item.bounded] using hb
    cases d with
    | zero => simp [Item.withinDepth] at hd
    | succ d =>
    have hd' : Item.withinDepthEntries d es = true := by simpa [Item.withinDepth] using hd
    have ⟨hinc, hs'⟩ : Item.strictlyIncreasing (es.map (·.1.encode)) = true ∧
        sortedEntries es = true := by simpa [sorted] using hsrt
    rw [item_data_map] at h
    obtain ⟨hp, hr⟩ := readHead_push (major := 5) (by omega) hlen h.left
    have hat := h.right
    rw [← size_eq_length] at hat
    have hle := hat.le_size' hp.2
    have hcount := length_le_pushEntries es
    obtain ⟨ys, hys, hq, hentries, hmap⟩ :=
      entries_ok es d input _ _ (UInt64.ofNat es.length).toNat (Nat.le_refl _) hp.2 none []
        (by simp [UInt64.toNat_ofNat_of_lt' hlen]) hbl hd' hs' (by simpa using hinc) hat
    have hend : pos + (Head.push .empty 5 es.length).size + (Item.pushEntries .empty es).size =
        pos + ((Item.map es).push .empty).size := by
      rw [size_eq_length ((Item.map es).push .empty), item_data_map, List.length_append,
        size_eq_length (Head.push .empty 5 es.length), size_eq_length (Item.pushEntries .empty es)]
      omega
    have hys' : ys.length < 2 ^ 64 := by rw [hys]; exact UInt64.toNat_lt _
    have hq' : pos < pos + ((Item.map es).push .empty).size ∧
        pos + ((Item.map es).push .empty).size ≤ input.size := by
      rw [← hend]; exact ⟨by omega, hq.2⟩
    refine ⟨Value.map ys hys', hq', ?_, by simp [Value.map, hmap]⟩
    unfold Decode.item
    rw [hr]
    simp only [Decode.Head.ofMajor]
    simp only [show (5 == 0) = false from rfl, show (5 == 1) = false from rfl,
      show (5 == 2) = false from rfl, show (5 == 3) = false from rfl,
      show (5 == 4) = false from rfl, Bool.false_eq_true, ↓reduceIte]
    simp only [UInt64.toNat_ofNat_of_lt' hlen]
    rw [ite_eq_left (by have := size_eq_length (Item.pushEntries .empty es); omega)]
    rw [hentries]
    simp only [Except.ok.injEq, Prod.mk.injEq, Subtype.mk.injEq]
    constructor <;> first | trivial | exact hend

/--
The decoder's array loop reads back any list of items it could have produced. It is the list half of
`item_ok`, stated with the loop's accumulator free so that induction on the list goes through.

The conditions on `xs` are those of `item_ok` for each element. With the elements written alone at
`pos`, `Decode.items` with `xs.length` remaining succeeds with a list `ys` whose items are those
already in `acc`, oldest first, followed by `xs`, ending just past the elements. `start`, `count`
and their proofs are the loop's bookkeeping and constrain nothing.
-/
theorem items_ok : (xs : List Item) → ∀ (d : Nat) (input : ByteArray) (start pos count : Nat)
    (hstart : start ≤ pos) (hpos : pos ≤ input.size) (acc : List Value)
    (hacc : acc.length + xs.length = count),
    Item.boundedList xs = true → Item.withinDepthList d xs = true → sortedList xs = true →
    At input pos (Item.pushList .empty xs).data.toList →
    ∃ ys hys hq, Decode.items input d start pos count hstart hpos xs.length acc hacc =
        .ok (⟨ys, hys⟩, ⟨pos + (Item.pushList .empty xs).size, hq⟩) ∧
      ys.map (·.item) = acc.reverse.map (·.item) ++ xs
  | [], d, input, start, pos, count, hstart, hpos, acc, hacc, _, _, _, _ => by
    refine ⟨acc.reverse, by simpa using hacc, by simpa [Item.pushList] using ⟨hstart, hpos⟩,
      ?_, by simp⟩
    unfold Decode.items
    simp [Item.pushList]
  | x :: xs, d, input, start, pos, count, hstart, hpos, acc, hacc, hb, hd, hs, h => by
    have ⟨hbx, hbl⟩ : x.bounded = true ∧ Item.boundedList xs = true := by
      simpa [Item.boundedList] using hb
    have ⟨hdx, hdl⟩ : x.withinDepth d = true ∧ Item.withinDepthList d xs = true := by
      simpa [Item.withinDepthList] using hd
    have ⟨hsx, hsl⟩ : sorted x = true ∧ sortedList xs = true := by simpa [sortedList] using hs
    have hdata : (Item.pushList .empty (x :: xs)).data.toList =
        (x.push .empty).data.toList ++ (Item.pushList .empty xs).data.toList := by
      simp only [Item.pushList]; rw [pushList_data]
    rw [hdata] at h
    obtain ⟨v, hp, hi, hv⟩ := item_ok x d input pos hbx hdx hsx h.left
    have hat := h.right
    rw [← size_eq_length] at hat
    obtain ⟨ys, hys, hq, hr, hmap⟩ := items_ok xs d input start (pos + (x.push .empty).size)
      count
      (by omega) hp.2 (v :: acc) (by simp at hacc ⊢; omega) hbl hdl hsl hat
    have hend : pos + (x.push .empty).size + (Item.pushList .empty xs).size =
        pos + (Item.pushList .empty (x :: xs)).size := by
      rw [size_eq_length (Item.pushList .empty (x :: xs)), hdata, List.length_append,
        size_eq_length (x.push .empty), size_eq_length (Item.pushList .empty xs)]
      omega
    refine ⟨ys, hys, hend ▸ hq, ?_, by simp [hmap, hv]⟩
    unfold Decode.items
    simp only [List.length_cons]
    rw [hi]
    simp only
    rw [hr]
    simp only [Except.ok.injEq, Prod.mk.injEq, Subtype.mk.injEq]
    constructor <;> first | trivial | exact hend
/--
The decoder's map loop reads back any list of entries it could have produced, provided the keys
strictly increase after the previous one. It is the map half of `item_ok`, and the one that
exercises the inline order check.

The conditions on `es` are those of `item_ok` for each value; the strictly increasing chain from
`previous` through every key's encoding is what lets every order check pass. With the entries
written alone at `pos`, `Decode.entries` succeeds with entries whose keys and items are those in
`acc`, oldest first, followed by `es`, ending just past them.
-/
theorem entries_ok : (es : List (Key × Item)) → ∀ (d : Nat) (input : ByteArray)
    (start pos count : Nat) (hstart : start ≤ pos) (hpos : pos ≤ input.size)
    (previous : Option ByteArray) (acc : List (Key × Value))
    (hacc : acc.length + es.length = count),
    Item.boundedEntries es = true → Item.withinDepthEntries d es = true →
    sortedEntries es = true →
    Item.strictlyIncreasing (previous.toList ++ es.map (·.1.encode)) = true →
    At input pos (Item.pushEntries .empty es).data.toList →
    ∃ ys hys hq, Decode.entries input d start pos count hstart hpos previous es.length acc hacc =
        .ok (⟨ys, hys⟩, ⟨pos + (Item.pushEntries .empty es).size, hq⟩) ∧
      ys.map (fun e => (e.1, e.2.item)) = acc.reverse.map (fun e => (e.1, e.2.item)) ++ es
  | [], d, input, start, pos, count, hstart, hpos, previous, acc, hacc, _, _, _, _, _ => by
    refine ⟨acc.reverse, by simpa using hacc,
      by simpa [Item.pushEntries] using ⟨hstart, hpos⟩, ?_, by simp⟩
    unfold Decode.entries
    simp [Item.pushEntries]
  | (k, x) :: es, d, input, start, pos, count, hstart, hpos, previous, acc, hacc, hb, hd, hs,
      hinc, h => by
    have ⟨hbx, hbl⟩ : x.bounded = true ∧ Item.boundedEntries es = true := by
      simpa [Item.boundedEntries] using hb
    have ⟨hdx, hdl⟩ : x.withinDepth d = true ∧ Item.withinDepthEntries d es = true := by
      simpa [Item.withinDepthEntries] using hd
    have ⟨hsx, hsl⟩ : sorted x = true ∧ sortedEntries es = true := by
      simpa [sortedEntries] using hs
    have hdata : (Item.pushEntries .empty ((k, x) :: es)).data.toList =
        k.encode.data.toList ++ (x.push .empty).data.toList ++
          (Item.pushEntries .empty es).data.toList := by
      simp only [Item.pushEntries]
      rw [pushEntries_data, push_data, key_data]
      simp
    rw [hdata] at h
    have hK := h.left.left
    have hX := h.left.right
    have hE := h.right
    rw [← size_eq_length] at hX
    obtain ⟨hkq, hk⟩ := readKey_ok k hK
    have hext : input.extract pos (pos + k.encode.size) = k.encode := by
      apply bytes_ext; rw [size_eq_length]; exact hK.extract
    have hinc0 : Item.strictlyIncreasing
        (previous.toList ++ k.encode :: es.map (·.1.encode)) = true := by simpa using hinc
    have hinc' : Item.strictlyIncreasing (k.encode :: es.map (·.1.encode)) = true := by
      cases previous with
      | none => simpa using hinc0
      | some p => exact strictlyIncreasing_tail (by simpa using hinc0)
    obtain ⟨v, hp, hi, hv⟩ := item_ok x d input (pos + k.encode.size) hbx hdx hsx hX
    have hE' : At input (pos + k.encode.size + (x.push .empty).size)
        (Item.pushEntries .empty es).data.toList := by
      have := hE
      simp only [List.length_append, ← size_eq_length] at this
      simpa [Nat.add_assoc] using this
    obtain ⟨ys, hys, hq, hr, hmap⟩ := entries_ok es d input start
      (pos + k.encode.size + (x.push .empty).size) count (by omega) hp.2
      (some (input.extract pos (pos + k.encode.size))) ((k, v) :: acc)
      (by simp at hacc ⊢; omega) hbl hdl hsl (by rw [hext]; simpa using hinc') hE'
    have hend : pos + k.encode.size + (x.push .empty).size + (Item.pushEntries .empty es).size =
        pos + (Item.pushEntries .empty ((k, x) :: es)).size := by
      rw [size_eq_length (Item.pushEntries .empty ((k, x) :: es)), hdata, List.length_append,
        List.length_append, size_eq_length k.encode, size_eq_length (x.push .empty),
        size_eq_length (Item.pushEntries .empty es)]
      omega
    refine ⟨ys, hys, hend ▸ hq, ?_, by simp [hmap, hv]⟩
    unfold Decode.entries
    simp only [List.length_cons]
    rw [hk]
    simp only
    rw [checkOrder_ok (l := es.map (·.1.encode)) (by rw [hext]; exact hinc0)]
    simp only
    rw [hi]
    simp only
    rw [hr]
    simp only [Except.ok.injEq, Prod.mk.injEq, Subtype.mk.injEq]
    constructor <;> first | trivial | exact hend
end

end Tests.Proofs
