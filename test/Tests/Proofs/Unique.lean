/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Tests.Proofs.Inverse

@[expose] public section

namespace Tests.Proofs
open Cbor

/-- What `Decode.item` guarantees of what it accepts, from positions at most `m` bytes from the
end. -/
def ItemInv (input : ByteArray) (m : Nat) : Prop :=
  ∀ d pos v q hq, input.size - pos ≤ m → Decode.item input d pos = .ok (v, ⟨q, hq⟩) →
    (v.item.push .empty).data.toList = (input.extract pos q).data.toList ∧
      sorted v.item = true ∧ v.item.withinDepth d = true

def ItemsInv (input : ByteArray) (m : Nat) : Prop :=
  ∀ d start pos count hstart hpos remaining acc hacc ys hys q hq, input.size - pos ≤ m →
    Decode.items input d start pos count hstart hpos remaining acc hacc =
      .ok (⟨ys, hys⟩, ⟨q, hq⟩) →
    ∃ zs, ys = acc.reverse ++ zs ∧ pos ≤ q ∧
      (Item.pushList .empty (zs.map (·.item))).data.toList = (input.extract pos q).data.toList ∧
      sortedList (zs.map (·.item)) = true ∧ Item.withinDepthList d (zs.map (·.item)) = true

def EntriesInv (input : ByteArray) (m : Nat) : Prop :=
  ∀ d start pos count hstart hpos previous remaining acc hacc ys hys q hq,
    input.size - pos ≤ m →
    Decode.entries input d start pos count hstart hpos previous remaining acc hacc =
      .ok (⟨ys, hys⟩, ⟨q, hq⟩) →
    ∃ zs, ys = acc.reverse ++ zs ∧ pos ≤ q ∧
      (Item.pushEntries .empty (zs.map fun e => (e.1, e.2.item))).data.toList =
        (input.extract pos q).data.toList ∧
      sortedEntries (zs.map fun e => (e.1, e.2.item)) = true ∧
      Item.withinDepthEntries d (zs.map fun e => (e.1, e.2.item)) = true ∧
      Item.strictlyIncreasing (previous.toList ++ zs.map (·.1.encode)) = true

/--
The decoder's item reader, from positions at most `m` bytes from the end, accepts only what the
encoder would write back exactly, sorted and within its depth, provided the loops are known to
behave for shorter remainders. It is one step of the strong induction in `inv_all`, separated out
because the loops at the same `m` depend on it.

`ih` gives `ItemInv`, `ItemsInv` and `EntriesInv` for every `m' < m`, and the conclusion is `ItemInv
input m`: whenever `Decode.item` succeeds from such a position, the value's encoding is the bytes it
consumed, its maps strictly increase, and its nesting is within the depth it was given. An array or
map reads its elements from past its head, so fewer bytes remain, which is where `ih` applies.
-/
theorem item_inv_step {input : ByteArray} {m : Nat}
    (ih : ∀ m' < m, ItemInv input m' ∧ ItemsInv input m' ∧ EntriesInv input m') :
    ItemInv input m := by
  intro d pos v q hq hm h
  unfold Decode.item at h
  split at h
  all_goals first | (simp at h; done) | skip
  · rename_i v' p hr
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨(readHead_inv hr).symm, ?_⟩
    rcases readHead_simple_inv hr with rfl | rfl | rfl <;> exact ⟨rfl, by cases d <;> rfl⟩
  · rename_i n p hr
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨by rw [readHead_inv hr]; rfl, rfl, by cases d <;> rfl⟩
  · rename_i n p hr
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨by rw [readHead_inv hr]; rfl, rfl, by cases d <;> rfl⟩
  · rename_i n p hr
    split at h
    · simp at h
    rename_i b hb q' hs
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨p, hp⟩ := p
    obtain ⟨rfl, rfl⟩ := readSlice_inv hs
    simp only at hq ⊢
    have hsize : (input.extract p (p + n.toNat)).size = n.toNat := by
      rw [ByteArray.size_extract, Nat.min_eq_left hq.2]; omega
    refine ⟨?_, rfl, by cases d <;> rfl⟩
    rw [extract_split input (Nat.le_of_lt hp.1) (Nat.le_add_right _ _), readHead_inv hr]
    simp [Value.bytes, Item.push, Head.byteString, headEncode, hsize]
  · rename_i n p hr
    split at h
    · simp at h
    rename_i s hs q' ht
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨p, hp⟩ := p
    obtain ⟨hs', rfl⟩ := readText_inv ht
    simp only at hq hs' ⊢
    have hlen : s.utf8ByteSize = n.toNat := by
      have := congrArg ByteArray.size hs'
      rw [ByteArray.size_extract, Nat.min_eq_left hq.2] at this
      simp at this
      omega
    refine ⟨?_, rfl, by cases d <;> rfl⟩
    rw [extract_split input (Nat.le_of_lt hp.1) (Nat.le_add_right _ _), readHead_inv hr, ← hs']
    simp [Value.text, Item.push, Head.textString, headEncode, hlen]
  · rename_i n p hp hr
    cases d with
    | zero => simp at h
    | succ d =>
    simp only at h
    split at h
    · rename_i hcount
      split at h
      · simp at h
      rename_i xs hxs q' hq' hitems
      simp only [Except.ok.injEq, Prod.mk.injEq, Subtype.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hm' : input.size - p < m := by omega
      obtain ⟨zs, hzs, hpq, hbytes, hsrt, hdep⟩ :=
        (ih _ hm').2.1 d p p n.toNat _ _ n.toNat [] _ xs hxs q' hq' (Nat.le_refl _) hitems
      simp only [List.reverse_nil, List.nil_append] at hzs
      subst hzs
      refine ⟨?_, by simpa [Value.array, sorted] using hsrt,
        by simpa [Value.array, Item.withinDepth] using hdep⟩
      simp only [Value.array]
      rw [item_data_array, extract_split input (Nat.le_of_lt hp.1) hpq, readHead_inv hr, hbytes,
        List.length_map, hxs]
      rfl
    · simp at h
  · rename_i n p hp hr
    cases d with
    | zero => simp at h
    | succ d =>
    simp only at h
    split at h
    · rename_i hcount
      split at h
      · simp at h
      rename_i es hes q' hq' hentries
      simp only [Except.ok.injEq, Prod.mk.injEq, Subtype.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hm' : input.size - p < m := by omega
      obtain ⟨zs, hzs, hpq, hbytes, hsrt, hdep, hinc⟩ :=
        (ih _ hm').2.2 d p p n.toNat _ _ none n.toNat [] _ es hes q' hq' (Nat.le_refl _)
          hentries
      simp only [List.reverse_nil, List.nil_append] at hzs
      subst hzs
      refine ⟨?_, ?_, by simpa [Value.map, Item.withinDepth] using hdep⟩
      · simp only [Value.map]
        rw [item_data_map, extract_split input (Nat.le_of_lt hp.1) hpq, readHead_inv hr, hbytes,
          List.length_map, hes]
        rfl
      · simp only [Value.map, sorted, Bool.and_eq_true]
        exact ⟨by simpa [List.map_map, Function.comp_def] using hinc, hsrt⟩
    · simp at h

/--
The decoder's array loop accepts only lists of items the encoder would write back exactly. It is the
step of `inv_all` for arrays, taking the item step at the same `m` as given, since the loop's first
item starts where the loop does.

With `ih` for shorter remainders and `ItemInv input m`, the conclusion is `ItemsInv input m`: a
successful run of `Decode.items` returns what was accumulated followed by new items whose encodings
are exactly the bytes consumed, each sorted and within depth.
-/
theorem items_inv_step {input : ByteArray} {m : Nat}
    (ih : ∀ m' < m, ItemInv input m' ∧ ItemsInv input m' ∧ EntriesInv input m')
    (hitem : ItemInv input m) : ItemsInv input m := by
  intro d start pos count hstart hpos remaining acc hacc ys hys q hq hm h
  unfold Decode.items at h
  split at h
  · simp only [Except.ok.injEq, Prod.mk.injEq, Subtype.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨[], by simp, Nat.le_refl _, by simp [Item.pushList], rfl, rfl⟩
  · rename_i r
    split at h
    · simp at h
    rename_i v p hp hi
    have ⟨hvb, hvs, hvd⟩ := hitem d pos v p hp hm hi
    have hm' : input.size - p < m := by omega
    obtain ⟨zs, hzs, hpq, hbytes, hsrt, hdep⟩ := (ih _ hm').2.1 _ _ _ _ _ _ _ _ _ _ _ _ _
      (Nat.le_refl _) h
    refine ⟨v :: zs, by simp [hzs], by omega, ?_, ?_, ?_⟩
    · simp only [List.map_cons, Item.pushList]
      rw [pushList_data, hvb, hbytes, ← extract_split input (Nat.le_of_lt hp.1) hpq]
    · simp [sortedList, hvs, hsrt]
    · simp [Item.withinDepthList, hvd, hdep]

/--
The decoder's map loop accepts only lists of entries the encoder would write back exactly, with keys
strictly increasing after the previous one. It is the step of `inv_all` for maps, and where the
inline order check becomes a property of the result.

With `ih` for shorter remainders and `ItemInv input m`, the conclusion is `EntriesInv input m`: a
successful run of `Decode.entries` returns what was accumulated followed by new entries whose
encodings are exactly the bytes consumed, whose values are sorted and within depth, and whose keys
continue a strictly increasing chain from `previous`.
-/
theorem entries_inv_step {input : ByteArray} {m : Nat}
    (ih : ∀ m' < m, ItemInv input m' ∧ ItemsInv input m' ∧ EntriesInv input m')
    (hitem : ItemInv input m) : EntriesInv input m := by
  intro d start pos count hstart hpos previous remaining acc hacc ys hys q hq hm h
  unfold Decode.entries at h
  split at h
  · simp only [Except.ok.injEq, Prod.mk.injEq, Subtype.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨[], by simp, Nat.le_refl _, by simp [Item.pushEntries], rfl, rfl, ?_⟩
    cases previous <;> rfl
  · rename_i r
    split at h
    · simp at h
    rename_i k kp hkp hk
    simp only at h
    split at h
    · simp at h
    rename_i hord
    split at h
    · simp at h
    rename_i v p hp hi
    have hkenc := readKey_inv hk
    have hkeq : input.extract pos kp = k.encode := bytes_ext hkenc.symm
    have ⟨hvb, hvs, hvd⟩ := hitem d kp v p hp (by omega) hi
    have hm' : input.size - p < m := by omega
    obtain ⟨zs, hzs, hpq, hbytes, hsrt, hdep, hinc⟩ :=
      (ih _ hm').2.2 _ _ _ _ _ _ _ _ _ _ _ _ _ _
      (Nat.le_refl _) h
    rw [hkeq] at hinc hord
    refine ⟨(k, v) :: zs, by simp [hzs], by omega, ?_, ?_, ?_, ?_⟩
    · simp only [List.map_cons, Item.pushEntries]
      rw [pushEntries_data, push_data, key_data, hkenc, hvb, hbytes]
      simp only [ByteArray.data_empty, Array.toList_empty, List.nil_append, List.append_assoc]
      rw [← extract_split input (Nat.le_of_lt hp.1) hpq,
        ← extract_split input (Nat.le_of_lt hkp.1) (by omega)]
    · simp [sortedEntries, hvs, hsrt]
    · simp [Item.withinDepthEntries, hvd, hdep]
    · have hlt := checkOrder_inv hord
      cases previous with
      | none => simpa using hinc
      | some p' =>
        simp only [Option.toList_some, List.map_cons, List.singleton_append] at hinc ⊢
        simp [Item.strictlyIncreasing, hlt p' rfl, hinc]

/--
For every bound on the bytes remaining, the decoder's item reader and both its loops accept only
what the encoder would write back exactly. The recursion terminates on the bytes remaining, and this
is the induction that follows it.

The conclusion is `ItemInv`, `ItemsInv` and `EntriesInv` for `input` and every `m`, by strong
induction on `m`; within each step the item reader is proved first because both loops call it at
their own starting position.
-/
theorem inv_all (input : ByteArray) :
    ∀ m, ItemInv input m ∧ ItemsInv input m ∧ EntriesInv input m := by
  intro m
  refine Nat.strongRecOn m ?_
  intro m ih
  have hitem := item_inv_step ih
  exact ⟨hitem, items_inv_step ih hitem, entries_inv_step ih hitem⟩

/--
A value `decode` accepts encodes, as written, to exactly the input, with every map strictly
increasing and nesting within the bound. It is the whole of what the inverse induction says about a
complete decode, from which the theorems that follow are read off.

The hypothesis says `decode input` produced `v`. The conclusion says `v.item` written alone is the
bytes of `input`, `sorted v.item` holds, and `v.withinDepth` holds. The trailing-bytes check is what
makes the first part about all of `input` rather than a prefix.
-/
theorem decode_inv {input : ByteArray} {v : Value} (h : decode input = .ok v) :
    (v.item.push .empty).data.toList = input.data.toList ∧ sorted v.item = true ∧
      v.withinDepth = true := by
  unfold decode at h
  split at h
  · simp at h
  rename_i v' q hpre
  split at h
  · rename_i hq
    simp only [Except.ok.injEq] at h
    subst h
    subst hq
    unfold decodePrefix at hpre
    split at hpre
    · simp at hpre
    rename_i w p hitem
    simp only [Except.ok.injEq, Prod.mk.injEq] at hpre
    obtain ⟨rfl, hp⟩ := hpre
    obtain ⟨p, hp'⟩ := p
    simp only at hp
    subst hp
    obtain ⟨hb, hs, hd⟩ := (inv_all input _).1 maxDepth 0 w _ hp' (Nat.le_refl _) hitem
    refine ⟨?_, hs, hd⟩
    rw [hb, ByteArray.extract_zero_size]
  · simp at h

mutual
/--
An item whose maps' keys strictly increase as held has no repeated key in any map. A strict order
has no ties, and this turns the decoder's order check into the property `Value.distinctKeys` names.

`sorted x` answers `true` when every map's key encodings strictly increase as held; the conclusion
is `x.distinctKeys`, which sorts each map's entries and checks the same, and finds them already in
order.
-/
theorem distinctKeys_of_sorted : (x : Item) → sorted x = true → x.distinctKeys = true
  | .array xs, h => by
    simp only [sorted] at h
    simp only [Item.distinctKeys]
    exact distinctKeysList_of_sorted xs h
  | .map es, h => by
    simp only [sorted, Bool.and_eq_true] at h
    simp only [Item.distinctKeys, Item.keysDistinct, Bool.and_eq_true]
    rw [List.mergeSort_of_pairwise (pairwise_of_strictlyIncreasing es h.1)]
    exact ⟨h.1, distinctKeysEntries_of_sorted es h.2⟩
  | .uint _, _ | .nint _, _ | .bytes _ _, _ | .text _ _, _ | .bool _, _ | .null, _ => rfl

/--
A list of items whose maps' keys strictly increase has no repeated key in any of them. It is the
list half of `distinctKeys_of_sorted`.

`sortedList xs` answers `true` when every map in every item of `xs` strictly increases; the
conclusion is `Item.distinctKeysList xs`.
-/
theorem distinctKeysList_of_sorted : (xs : List Item) → sortedList xs = true →
    Item.distinctKeysList xs = true
  | [], _ => rfl
  | x :: xs, h => by
    simp only [sortedList, Bool.and_eq_true] at h
    simp only [Item.distinctKeysList, Bool.and_eq_true]
    exact ⟨distinctKeys_of_sorted x h.1, distinctKeysList_of_sorted xs h.2⟩

/--
Entries whose values' maps strictly increase have no repeated key in any of those maps. It is the
map half of `distinctKeys_of_sorted`, for the values.

`sortedEntries es` answers `true` when every map in every value of `es` strictly increases; the
conclusion is `Item.distinctKeysEntries es`.
-/
theorem distinctKeysEntries_of_sorted : (es : List (Key × Item)) → sortedEntries es = true →
    Item.distinctKeysEntries es = true
  | [], _ => rfl
  | (k, x) :: es, h => by
    simp only [sortedEntries, Bool.and_eq_true] at h
    simp only [Item.distinctKeysEntries, Bool.and_eq_true]
    exact ⟨distinctKeys_of_sorted x h.1, distinctKeysEntries_of_sorted es h.2⟩
end

/--
CBOR-10.3: if `decode` accepts some bytes and yields a value, encoding that value returns exactly
those bytes. Canonicity is therefore a property of the decoder: two different byte strings cannot
decode to one value, so a signature over accepted bytes covers what was read.

The hypothesis is that `decode input` produced `v`, with nothing further assumed about `input`. The
conclusion is that `v.encode`, which sorts maps before writing, is `input` byte for byte. It holds
because the decoder refuses non-minimal heads, indefinite lengths, unsorted or repeated keys,
invalid UTF-8 and trailing bytes, so what remains is exactly the encoder's output.
-/
theorem encode_decode {input : ByteArray} {v : Value} (h : decode input = .ok v) :
    v.encode = input := by
  obtain ⟨hb, hs, _⟩ := decode_inv h
  apply bytes_ext
  simp only [Value.encode, Item.encode]
  rw [normalise_of_sorted v.item hs, hb]

/--
CBOR-10.2, first clause: every value the decoder produces is normalised. With `normalise_normalise`
and `decode_encode`, it says a decoded value round-trips to itself exactly, not merely to a
reordering of itself.

The hypothesis is that `decode input` produced `v`; the conclusion is that sorting every map in
`v.item` changes nothing.
-/
theorem decode_normalised {input : ByteArray} {v : Value} (h : decode input = .ok v) :
    v.item.normalise = v.item :=
  normalise_of_sorted v.item (decode_inv h).2.1

/--
Every value the decoder produces has distinct keys in every map. It discharges the distinct-keys
hypothesis of `decode_encode` for decoded values, which is why that hypothesis is not doing the work
there.

The hypothesis is that `decode input` produced `v`; the conclusion is `v.distinctKeys`, the
predicate `decode_encode` assumes.
-/
theorem decode_distinctKeys {input : ByteArray} {v : Value} (h : decode input = .ok v) :
    v.distinctKeys = true :=
  distinctKeys_of_sorted v.item (decode_inv h).2.1

/--
Every value the decoder produces is nested within the depth bound. It discharges the depth
hypothesis of `decode_encode` for decoded values.

The hypothesis is that `decode input` produced `v`; the conclusion is `v.withinDepth`, the predicate
`decode_encode` assumes, which admits nesting up to `maxDepth`.
-/
theorem decode_withinDepth {input : ByteArray} {v : Value} (h : decode input = .ok v) :
    v.withinDepth = true :=
  (decode_inv h).2.2

end Tests.Proofs
