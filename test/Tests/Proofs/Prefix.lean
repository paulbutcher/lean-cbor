/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Tests.Proofs.Unique

@[expose] public section

namespace Tests.Proofs
open Cbor

/--
CBOR-5.2: `decodePrefix` finds an encoded value wherever it sits, whatever comes before or after it,
and reports where it ends. WebAuthn's `authenticatorData` puts a credential public key between fixed
fields and optional extension data, and this is what makes the key's end, and so the start of what
follows, trustworthy.

`v.distinctKeys` and `v.withinDepth` are the hypotheses of `decode_encode`, and are not doing the
work for the same reason: `decode_distinctKeys` and `decode_withinDepth` show every decoded value
satisfies them, and the depth bound admits nesting up to 1024. `pre ++ v.encode ++ rest` is the
encoding embedded in arbitrary bytes, and `pre.size` is the offset at which it starts. The
conclusion says `decodePrefix` succeeds with `v` normalised and the offset just past the encoding.
-/
theorem decodePrefix_encode (v : Value) (hk : v.distinctKeys = true) (hd : v.withinDepth = true)
    (pre rest : ByteArray) :
    (decodePrefix (pre ++ v.encode ++ rest) pre.size).map (fun r => (r.1.item, r.2)) =
      .ok (v.item.normalise, pre.size + v.encode.size) := by
  have hb := bounded_normalise v.item v.isBounded
  have hd' := withinDepth_normalise v.item maxDepth hd
  have hs := sorted_normalise v.item hk
  have hat : At (pre ++ v.encode ++ rest) pre.size (v.item.normalise.push .empty).data.toList := by
    refine ⟨rest.data.toList, ?_⟩
    rw [data_append, data_append, size_eq_length pre, List.append_assoc, List.drop_left]
    rfl
  obtain ⟨w, hp, hi, hw⟩ := item_ok _ maxDepth _ _ hb hd' hs hat
  simp only [decodePrefix]
  rw [hi]
  simp [Except.map, hw, Value.encode, Item.encode]

/--
Whatever `decodePrefix` accepts, re-encoding gives exactly the bytes it consumed. It is CBOR-10.3
for a prefix: the item a consumer extracts from a larger structure has one encoding, and it is the
bytes that were there.

The hypothesis is that `decodePrefix input offset` produced `v` ending at `q`, with nothing assumed
about `input`; the conclusion is that `v.encode` is the slice of `input` from `offset` to `q`.
-/
theorem decodePrefix_unique {input : ByteArray} {offset q : Nat} {v : Value}
    (h : decodePrefix input offset = .ok (v, q)) : v.encode = input.extract offset q := by
  unfold decodePrefix at h
  split at h
  · simp at h
  rename_i w p hitem
  simp only [Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  obtain ⟨p, hp⟩ := p
  obtain ⟨hb, hs, _⟩ := (inv_all input _).1 maxDepth offset w p hp (Nat.le_refl _) hitem
  apply bytes_ext
  simp only [Value.encode, Item.encode]
  rw [normalise_of_sorted w.item hs, hb]

/--
CBOR-5.1: `decode` refuses any bytes after a complete item, and says where they begin. A decoder
that ignored them would accept two different inputs as one value, which is the parsing differential
this library exists to prevent.

`v.distinctKeys` and `v.withinDepth` are the hypotheses of `decode_encode`, satisfied by every
decoded value by `decode_distinctKeys` and `decode_withinDepth`. `rest` is any nonempty bytes; the
conclusion is that `decode` of the encoding followed by `rest` is the `trailingBytes` error at the
offset where `rest` begins.
-/
theorem decode_trailing (v : Value) (hk : v.distinctKeys = true) (hd : v.withinDepth = true)
    (rest : ByteArray) (hr : rest.size ≠ 0) :
    decode (v.encode ++ rest) = .error ⟨.trailingBytes, v.encode.size⟩ := by
  have h := decodePrefix_encode v hk hd .empty rest
  simp only [ByteArray.empty_append, ByteArray.size_empty, Nat.zero_add] at h
  unfold decode
  split
  · rename_i e he
    rw [he] at h
    simp [Except.map] at h
  · rename_i w p hpre
    rw [hpre] at h
    simp only [Except.map, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨_, rfl⟩ := h
    rw [if_neg (by simp [ByteArray.size_append, hr])]

end Tests.Proofs
