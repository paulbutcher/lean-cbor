/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Tests.Proofs.RoundTrip

@[expose] public section

namespace Tests.Proofs
open Cbor

instance : Std.TransCmp Order.compareLists := by
  unfold Order.compareLists; infer_instance

/--
The encoder's sort relation is whether the CTAP2 comparison of two keys says less or equal. It
connects the relation `List.mergeSort` is given to the comparison core's ordering lemmas apply to.

`Item.entryPrecedes a b` answers `true` when `a`'s key may precede `b`'s; the right side asks
whether `Order.compareLists` on their encodings is `.lt` or `.eq`.
-/
theorem entryPrecedes_eq (a b : Key × Item) :
    Item.entryPrecedes a b =
      (Order.compareLists a.1.encode.data.toList b.1.encode.data.toList).isLE := by
  simp only [Item.entryPrecedes, Order.compareEncoded]
  cases Order.compareLists _ _ <;> rfl

/--
The sort relation is transitive. Sorting gives a sorted result only for a transitive relation, so
without this nothing could be said about the order `normalise` produces.

If `a`'s key may precede `b`'s and `b`'s may precede `c`'s, then `a`'s may precede `c`'s.
-/
theorem entryPrecedes_trans (a b c : Key × Item) :
    Item.entryPrecedes a b → Item.entryPrecedes b c → Item.entryPrecedes a c := by
  simp only [entryPrecedes_eq]
  exact Std.TransCmp.isLE_trans

/--
Any two entries are comparable under the sort relation. Sorting gives a sorted result only for a
total relation, so this and transitivity together are what make `normalise`'s output sorted.

For every `a` and `b`, at least one of `a`'s key may precede `b`'s or `b`'s may precede `a`'s.
-/
theorem entryPrecedes_total (a b : Key × Item) :
    (Item.entryPrecedes a b || Item.entryPrecedes b a) = true := by
  simp only [entryPrecedes_eq]
  rw [Std.OrientedCmp.eq_swap (cmp := Order.compareLists) (a := a.1.encode.data.toList)]
  cases Order.compareLists _ _ <;> rfl

/--
Sorting already sorted entries changes nothing. It is what makes normalising twice the same as
normalising once.

The left side sorts `l` and then sorts the result; the right side sorts `l` once. They agree because
the first sort's output is sorted, by transitivity and totality, and `mergeSort` leaves a sorted
list alone.
-/
theorem mergeSort_mergeSort (l : List (Key × Item)) :
    (l.mergeSort Item.entryPrecedes).mergeSort Item.entryPrecedes =
      l.mergeSort Item.entryPrecedes :=
  List.mergeSort_of_pairwise
    (List.pairwise_mergeSort entryPrecedes_trans entryPrecedes_total l)

def normaliseValue (e : Key × Item) : Key × Item := (e.1, e.2.normalise)

/--
Normalising a list of items normalises each in place. It replaces the mutual recursion with
`List.map`, whose lemmas the proofs use.

`Item.normaliseList xs` is the recursion `normalise` uses on an array's elements, and `xs.map
Item.normalise` the same thing stated with the library function.
-/
theorem normaliseList_eq (xs : List Item) : Item.normaliseList xs = xs.map Item.normalise := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [Item.normaliseList, ih]

/--
Normalising a list of map entries normalises each value in place and leaves keys and order alone. It
replaces the mutual recursion with `List.map`, whose lemmas the proofs use.

`Item.normaliseEntries es` is the recursion `normalise` uses on a map's entries before sorting them,
and `es.map normaliseValue` the same thing stated with the library function.
-/
theorem normaliseEntries_eq (es : List (Key × Item)) :
    Item.normaliseEntries es = es.map normaliseValue := by
  induction es with
  | nil => rfl
  | cons e es ih => obtain ⟨k, x⟩ := e; simp [Item.normaliseEntries, ih, normaliseValue]

/--
Sorting map entries commutes with normalising their values. The order looks only at keys, which
normalising never touches, so it does not matter which is done first, and the proofs need both
orders.

The left side normalises every value and then sorts; the right side sorts and then normalises every
value. Both sorts use `Item.entryPrecedes`, which answers the same for an entry and its normalised
form.
-/
theorem mergeSort_normalise (es : List (Key × Item)) :
    (es.map normaliseValue).mergeSort Item.entryPrecedes =
      (es.mergeSort Item.entryPrecedes).map normaliseValue :=
  (List.map_mergeSort (f := normaliseValue) (r := Item.entryPrecedes) (s := Item.entryPrecedes)
    (l := es) (fun _ _ _ _ => rfl)).symm

/--
Checking a list of items against a depth is checking each item. It turns the mutual recursion into
`List.all`, which is how the depth of a map's sorted entries is related to that of the entries
before sorting.

`Item.withinDepthList d xs` answers `true` when every item nests at most `d` deep, and the right
side asks the same with the library function.
-/
theorem withinDepthList_eq_all (d : Nat) (xs : List Item) :
    Item.withinDepthList d xs = xs.all (Item.withinDepth d) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [Item.withinDepthList, ih]

/--
Checking a list of map entries against a depth is checking each value. It turns the mutual recursion
into `List.all`, which survives the reordering a sort performs.

`Item.withinDepthEntries d es` answers `true` when every value nests at most `d` deep, and the right
side asks the same with the library function; keys never nest.
-/
theorem withinDepthEntries_eq_all (d : Nat) (es : List (Key × Item)) :
    Item.withinDepthEntries d es = es.all (fun e => e.2.withinDepth d) := by
  induction es with
  | nil => rfl
  | cons e es ih => obtain ⟨k, x⟩ := e; simp [Item.withinDepthEntries, ih]

/--
Asking that every value in a list of entries is sorted is asking it of each entry. It turns the
mutual recursion into `List.all`, which survives the reordering a sort performs.

`sortedEntries es` answers `true` when every value's maps strictly increase, and the right side asks
the same with the library function.
-/
theorem sortedEntries_eq_all (es : List (Key × Item)) :
    sortedEntries es = es.all (fun e => sorted e.2) := by
  induction es with
  | nil => rfl
  | cons e es ih => obtain ⟨k, x⟩ := e; simp [sortedEntries, ih]

/--
Asking that every item in a list is sorted is asking it of each item. It turns the mutual recursion
into `List.all`.

`sortedList xs` answers `true` when every item's maps strictly increase, and the right side asks the
same with the library function.
-/
theorem sortedList_eq_all (xs : List Item) : sortedList xs = xs.all sorted := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [sortedList, ih]

mutual
/--
Normalising keeps every length within what a head can hold. Normalising only reorders map entries,
so no count changes, and this is what lets the normalised item be decoded.

`x.bounded` answers `true` when every length in `x` is below `2 ^ 64`; the conclusion says the same
of `x.normalise`.
-/
theorem bounded_normalise : (x : Item) → x.bounded = true → x.normalise.bounded = true
  | .array xs, h => by
    simp only [Item.bounded, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [Item.normalise, Item.bounded, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨by simpa [normaliseList_eq] using h.1, boundedList_normalise xs h.2⟩
  | .map es, h => by
    simp only [Item.bounded, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [Item.normalise, Item.bounded, Bool.and_eq_true, decide_eq_true_eq]
    have := boundedEntries_normalise es h.2
    simp only [Item.boundedEntries_eq_all, List.all_eq_true] at this ⊢
    exact ⟨by simpa [normaliseEntries_eq] using h.1,
      fun e he => this e (List.mem_mergeSort.mp he)⟩
  | .uint _, h | .nint _, h | .bytes _ _, h | .text _ _, h | .bool _, h | .null, h => by
    simpa [Item.normalise] using h

/--
Normalising a list of items keeps every length within what a head can hold. It is the list half of
`bounded_normalise`.

`Item.boundedList xs` answers `true` when every item of `xs` is bounded; the conclusion says the
same after normalising each.
-/
theorem boundedList_normalise : (xs : List Item) → Item.boundedList xs = true →
    Item.boundedList (Item.normaliseList xs) = true
  | [], _ => rfl
  | x :: xs, h => by
    simp only [Item.boundedList, Bool.and_eq_true] at h
    simp only [Item.normaliseList, Item.boundedList, Bool.and_eq_true]
    exact ⟨bounded_normalise x h.1, boundedList_normalise xs h.2⟩

/--
Normalising the values of a list of map entries keeps every length within what a head can hold. It
is the map half of `bounded_normalise`.

`Item.boundedEntries es` answers `true` when every value of `es` is bounded; the conclusion says the
same after normalising each value.
-/
theorem boundedEntries_normalise : (es : List (Key × Item)) → Item.boundedEntries es = true →
    Item.boundedEntries (Item.normaliseEntries es) = true
  | [], _ => rfl
  | (k, x) :: es, h => by
    simp only [Item.boundedEntries, Bool.and_eq_true] at h
    simp only [Item.normaliseEntries, Item.boundedEntries, Bool.and_eq_true]
    exact ⟨bounded_normalise x h.1, boundedEntries_normalise es h.2⟩
end

mutual
/--
Normalising does not deepen nesting. Sorting reorders entries without moving them between levels,
and this is what lets a value within the depth bound still be decoded once normalised.

`x.withinDepth d` answers `true` when arrays and maps in `x` nest at most `d` deep; the conclusion
says the same of `x.normalise`, for every `d`.
-/
theorem withinDepth_normalise : (x : Item) → ∀ d, x.withinDepth d = true →
    x.normalise.withinDepth d = true
  | .array xs, d, h => by
    cases d with
    | zero => simp [Item.withinDepth] at h
    | succ d =>
      simp only [Item.withinDepth] at h
      simp only [Item.normalise, Item.withinDepth]
      exact withinDepthList_normalise xs d h
  | .map es, d, h => by
    cases d with
    | zero => simp [Item.withinDepth] at h
    | succ d =>
      simp only [Item.withinDepth] at h
      simp only [Item.normalise, Item.withinDepth]
      have := withinDepthEntries_normalise es d h
      simp only [withinDepthEntries_eq_all, List.all_eq_true] at this ⊢
      exact fun e he => this e (List.mem_mergeSort.mp he)
  | .uint _, _, h | .nint _, _, h | .bytes _ _, _, h | .text _ _, _, h | .bool _, _, h
  | .null, _, h => by simpa [Item.normalise] using h

/--
Normalising a list of items does not deepen nesting. It is the list half of `withinDepth_normalise`.

`Item.withinDepthList d xs` answers `true` when every item of `xs` nests at most `d` deep; the
conclusion says the same after normalising each.
-/
theorem withinDepthList_normalise : (xs : List Item) → ∀ d, Item.withinDepthList d xs = true →
    Item.withinDepthList d (Item.normaliseList xs) = true
  | [], _, _ => rfl
  | x :: xs, d, h => by
    simp only [Item.withinDepthList, Bool.and_eq_true] at h
    simp only [Item.normaliseList, Item.withinDepthList, Bool.and_eq_true]
    exact ⟨withinDepth_normalise x d h.1, withinDepthList_normalise xs d h.2⟩

/--
Normalising the values of a list of map entries does not deepen nesting. It is the map half of
`withinDepth_normalise`.

`Item.withinDepthEntries d es` answers `true` when every value of `es` nests at most `d` deep; the
conclusion says the same after normalising each value.
-/
theorem withinDepthEntries_normalise : (es : List (Key × Item)) → ∀ d,
    Item.withinDepthEntries d es = true →
    Item.withinDepthEntries d (Item.normaliseEntries es) = true
  | [], _, _ => rfl
  | (k, x) :: es, d, h => by
    simp only [Item.withinDepthEntries, Bool.and_eq_true] at h
    simp only [Item.normaliseEntries, Item.withinDepthEntries, Bool.and_eq_true]
    exact ⟨withinDepth_normalise x d h.1, withinDepthEntries_normalise es d h.2⟩
end

mutual
/--
Normalising an item with distinct keys leaves every map's keys strictly increasing. This is the
property the decoder's inline order check demands, and so the reason the encoder's output is
accepted.

`x.distinctKeys` answers `true` when no map in `x` holds a key twice, which is the check
`keysDistinct` makes on the entries in the order `normalise` sorts them. The conclusion `sorted
x.normalise` says every map in the normalised item has strictly increasing key encodings. Without
distinct keys it fails, since a repeated key sorts beside itself and the order is then not strict.
-/
theorem sorted_normalise : (x : Item) → x.distinctKeys = true → sorted x.normalise = true
  | .array xs, h => by
    simp only [Item.distinctKeys] at h
    simp only [Item.normalise, sorted]
    exact sortedList_normalise xs h
  | .map es, h => by
    simp only [Item.distinctKeys, Bool.and_eq_true] at h
    simp only [Item.normalise, sorted, Bool.and_eq_true]
    constructor
    · rw [normaliseEntries_eq, mergeSort_normalise, List.map_map]
      exact h.1
    · have := sortedEntries_normalise es h.2
      simp only [sortedEntries_eq_all, List.all_eq_true] at this ⊢
      exact fun e he => this e (List.mem_mergeSort.mp he)
  | .uint _, _ | .nint _, _ | .bytes _ _, _ | .text _ _, _ | .bool _, _ | .null, _ => by
    simp [Item.normalise, sorted]

/--
Normalising a list of items with distinct keys leaves every map in them strictly increasing. It is
the list half of `sorted_normalise`.

`Item.distinctKeysList xs` answers `true` when no map in any item of `xs` repeats a key; the
conclusion is `sortedList` of the normalised items.
-/
theorem sortedList_normalise : (xs : List Item) → Item.distinctKeysList xs = true →
    sortedList (Item.normaliseList xs) = true
  | [], _ => rfl
  | x :: xs, h => by
    simp only [Item.distinctKeysList, Bool.and_eq_true] at h
    simp only [Item.normaliseList, sortedList, Bool.and_eq_true]
    exact ⟨sorted_normalise x h.1, sortedList_normalise xs h.2⟩

/--
Normalising the values of entries with distinct keys leaves every map in those values strictly
increasing. It is the map half of `sorted_normalise`, for the values; the keys themselves are dealt
with where the entries are sorted.

`Item.distinctKeysEntries es` answers `true` when no map in any value of `es` repeats a key; the
conclusion is `sortedEntries` of the entries with their values normalised.
-/
theorem sortedEntries_normalise : (es : List (Key × Item)) →
    Item.distinctKeysEntries es = true →
    sortedEntries (Item.normaliseEntries es) = true
  | [], _ => rfl
  | (k, x) :: es, h => by
    simp only [Item.distinctKeysEntries, Bool.and_eq_true] at h
    simp only [Item.normaliseEntries, sortedEntries, Bool.and_eq_true]
    exact ⟨sorted_normalise x h.1, sortedEntries_normalise es h.2⟩
end

end Tests.Proofs
