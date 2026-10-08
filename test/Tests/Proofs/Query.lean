/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cbor

@[expose] public section

namespace Tests.Proofs
open Cbor

/--
Viewing an array built with `Value.array` gives back the values it was built from. Values hold an
unrestricted tree underneath, and this is what shows the view loses nothing in returning from it.

`Value.array xs h` builds the array, `h` being the bound a head can declare; the equation says its
view is `.array xs`, the same values in the same order.
-/
theorem view_array (xs : List Value) (h : xs.length < 2 ^ 64) :
    (Value.array xs h).view = .array xs := by
  simp only [Value.array, Value.view, List.attach_map, List.map_map]
  congr 1
  apply List.ext_getElem <;> simp

/--
Viewing a map built with `Value.map` gives back the entries it was built from, in the order given.
Queries read maps through this view, so it is what makes them answer about the map the caller built.

`Value.map es h` builds the map, `h` being the bound a head can declare; the equation says its view
is `.map es`, unsorted and unchanged.
-/
theorem view_map (es : List (Key × Value)) (h : es.length < 2 ^ 64) :
    (Value.map es h).view = .map es := by
  simp only [Value.map, Value.view, List.attach_map, List.map_map]
  congr 1
  apply List.ext_getElem <;> simp

/--
Looking a key up in a map takes the first entry with that key, and reports absence when there is
none. It is CBOR-8.3 for hand-built maps, which may repeat a key; a decoded map never does, by
`decode_distinctKeys`.

`(Value.map es h).find k` is the lookup; the right side searches `es` in order for the first entry
whose key is `k`, answering its value, or `missing k` if no entry has it.
-/
theorem find_map (es : List (Key × Value)) (h : es.length < 2 ^ 64) (k : Key) :
    (Value.map es h).find k =
      match es.find? (·.1 == k) with
      | some (_, w) => .ok w
      | none => .error (.missing k) := by
  unfold Value.find
  simp only [Value.asMap, view_map]
  rfl

/--
A lookup reports a key as absent exactly when no entry has that key. It is the half of CBOR-8.2 that
concerns absence: `missing` is never the answer for a key that is present, so a caller seeing it
knows the key is not there rather than holding the wrong kind of value.

The left side says the lookup in the map built from `es` failed with `missing k`; the right side
says every entry's key differs from `k`. The equivalence holds for every list of entries and every
key.
-/
theorem find_missing (es : List (Key × Value)) (h : es.length < 2 ^ 64) (k : Key) :
    (Value.map es h).find k = .error (.missing k) ↔ ∀ e ∈ es, e.1 ≠ k := by
  rw [find_map]
  split
  · rename_i w hf
    simp only [reduceCtorEq, false_iff, Classical.not_forall, Classical.not_not]
    have := List.find?_some hf
    exact ⟨_, List.mem_of_find?_eq_some hf, by simpa using this⟩
  · rename_i hf
    simp only [true_iff]
    intro e he hk
    have := List.find?_eq_none.mp hf e he
    simp_all

end Tests.Proofs
