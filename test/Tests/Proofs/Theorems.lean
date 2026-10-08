/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Tests.Proofs.Normalise

@[expose] public section

namespace Tests.Proofs
open Cbor

/--
CBOR-10.1: decoding a value's encoding gives back the value with its maps sorted. It is the round
trip for the encoder, stated against the normalisation because `encode` sorts maps (CBOR-7.3), and
it is what makes the encoder safe to hand bytes to a verifier using the same decoder.

`v.distinctKeys` says no map at any depth repeats a key, and `v.withinDepth` says nesting is within
`maxDepth`. `decode v.encode` is the decoder run on the encoder's output, mapped to the underlying
item, and `v.item.normalise` is `v` with every map's entries sorted into canonical order. The depth
hypothesis is not vacuous: it admits every value nesting up to 1024 deep, which is every value the
decoder itself can produce. The distinct-keys hypothesis is not doing the work either: a value the
decoder produces never repeats a key, since the decoder refuses a repeated key (CBOR-5.3); that is
not yet proved here and rests on the tests of that refusal.
-/
theorem decode_encode (v : Value) (hk : v.distinctKeys = true) (hd : v.withinDepth = true) :
    (decode v.encode).map (·.item) = .ok v.item.normalise := by
  have hb := bounded_normalise v.item v.isBounded
  have hd' := withinDepth_normalise v.item maxDepth hd
  have hs := sorted_normalise v.item hk
  have hat : At (v.item.normalise.push .empty) 0 (v.item.normalise.push .empty).data.toList :=
    ⟨[], by simp⟩
  obtain ⟨w, hp, hi, hw⟩ := item_ok _ maxDepth _ 0 hb hd' hs hat
  simp only [Value.encode, Item.encode, decode, decodePrefix]
  rw [hi]
  simp only [Nat.zero_add, ↓reduceIte]
  simp [Except.map, hw]

mutual
/--
Normalising a normalised item changes nothing. It is the second clause of CBOR-10.2, and what makes
the normalised value in CBOR-10.1 a fixed form rather than one step of a process.

`x.normalise.normalise` is `x` normalised twice and `x.normalise` once; they are equal for every
item, repeated keys included, since sorting a sorted list leaves it alone.
-/
theorem normalise_normalise : (x : Item) → x.normalise.normalise = x.normalise
  | .array xs => by
    simp only [Item.normalise]
    rw [normaliseList_normalise xs]
  | .map es => by
    simp only [Item.normalise]
    rw [normaliseEntries_eq ((Item.normaliseEntries es).mergeSort Item.entryPrecedes),
      ← mergeSort_normalise, ← normaliseEntries_eq, normaliseEntries_normalise es,
      mergeSort_mergeSort]
  | .uint _ | .nint _ | .bytes _ _ | .text _ _ | .bool _ | .null => rfl

/--
Normalising a normalised list of items changes nothing. It is the list half of
`normalise_normalise`.

`Item.normaliseList` applied twice to `xs` equals it applied once.
-/
theorem normaliseList_normalise : (xs : List Item) →
    Item.normaliseList (Item.normaliseList xs) = Item.normaliseList xs
  | [] => rfl
  | x :: xs => by
    simp only [Item.normaliseList]
    rw [normalise_normalise x, normaliseList_normalise xs]

/--
Normalising the values of entries whose values are normalised changes nothing. It is the map half of
`normalise_normalise`, before sorting.

`Item.normaliseEntries` applied twice to `es` equals it applied once.
-/
theorem normaliseEntries_normalise : (es : List (Key × Item)) →
    Item.normaliseEntries (Item.normaliseEntries es) = Item.normaliseEntries es
  | [] => rfl
  | (k, x) :: es => by
    simp only [Item.normaliseEntries]
    rw [normalise_normalise x, normaliseEntries_normalise es]
end

/--
Entries whose key encodings strictly increase from each to the next are in sorted order throughout.
The decoder checks only neighbours, and sorting is stated over every pair, so this is what connects
the two.

`Item.strictlyIncreasing` on the key encodings answers `true` when each precedes the next; the
conclusion says every earlier entry may precede every later one under `Item.entryPrecedes`, by
transitivity.
-/
theorem pairwise_of_strictlyIncreasing : (l : List (Key × Item)) →
    Item.strictlyIncreasing (l.map (·.1.encode)) = true →
      l.Pairwise (fun a b => Item.entryPrecedes a b = true)
  | [], _ => .nil
  | [_], _ => List.pairwise_singleton _ _
  | a :: b :: l, h => by
    have hab : Item.entryPrecedes a b = true := by
      simp only [List.map_cons, Item.strictlyIncreasing, Bool.and_eq_true, beq_iff_eq] at h
      simp [Item.entryPrecedes, h.1]
    have hrest := pairwise_of_strictlyIncreasing (b :: l) (strictlyIncreasing_tail h)
    refine List.Pairwise.cons (fun c hc => ?_) hrest
    rcases List.mem_cons.mp hc with rfl | hc
    · exact hab
    · exact entryPrecedes_trans _ _ _ hab (List.rel_of_pairwise_cons hrest hc)

mutual
/--
An item whose maps' keys already strictly increase is its own normalisation. Together with a proof
that the decoder produces only such items, it is the first clause of CBOR-10.2: a decoded value
round-trips to itself exactly.

`sorted x` answers `true` when every map in `x` has strictly increasing key encodings as held; the
conclusion says `x.normalise` is `x`, because sorting a list already in order leaves it alone.
-/
theorem normalise_of_sorted : (x : Item) → sorted x = true → x.normalise = x
  | .array xs, h => by
    simp only [sorted] at h
    simp only [Item.normalise]
    rw [normaliseList_of_sorted xs h]
  | .map es, h => by
    simp only [sorted, Bool.and_eq_true] at h
    simp only [Item.normalise]
    rw [normaliseEntries_of_sorted es h.2, List.mergeSort_of_pairwise
      (pairwise_of_strictlyIncreasing es h.1)]
  | .uint _, _ | .nint _, _ | .bytes _ _, _ | .text _ _, _ | .bool _, _ | .null, _ => rfl

/--
A list of items whose maps already strictly increase is its own normalisation. It is the list half
of `normalise_of_sorted`.

`sortedList xs` answers `true` when every map in every item of `xs` strictly increases; the
conclusion says `Item.normaliseList xs` is `xs`.
-/
theorem normaliseList_of_sorted : (xs : List Item) → sortedList xs = true →
    Item.normaliseList xs = xs
  | [], _ => rfl
  | x :: xs, h => by
    simp only [sortedList, Bool.and_eq_true] at h
    simp only [Item.normaliseList]
    rw [normalise_of_sorted x h.1, normaliseList_of_sorted xs h.2]

/--
Entries whose values' maps already strictly increase are their own normalisation, before sorting. It
is the map half of `normalise_of_sorted`.

`sortedEntries es` answers `true` when every map in every value of `es` strictly increases; the
conclusion says `Item.normaliseEntries es` is `es`.
-/
theorem normaliseEntries_of_sorted : (es : List (Key × Item)) → sortedEntries es = true →
    Item.normaliseEntries es = es
  | [], _ => rfl
  | (k, x) :: es, h => by
    simp only [sortedEntries, Bool.and_eq_true] at h
    simp only [Item.normaliseEntries]
    rw [normalise_of_sorted x h.1, normaliseEntries_of_sorted es h.2]
end

end Tests.Proofs
