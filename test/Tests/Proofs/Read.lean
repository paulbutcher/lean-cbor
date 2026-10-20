/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Tests.Proofs.Head

@[expose] public section

namespace Tests.Proofs
open Cbor

/--
Two byte arrays with the same bytes are equal. It lets a list-level fact about a slice become the
equality of byte arrays that values are built from.

The hypothesis says the lists of bytes agree, and the conclusion is equality of the arrays
themselves.
-/
theorem bytes_ext {a b : ByteArray} (h : a.data.toList = b.data.toList) : a = b :=
  ByteArray.ext (Array.ext' h)

/--
Writing a key onto a buffer appends the key's encoding. The decoder compares keys by their
encodings, so this is what ties the key the encoder writes to the bytes the decoder compares.

`k.push out` writes `k` onto `out`, and `k.encode` is `k` written alone; the equation says the first
is `out` followed by the second.
-/
theorem key_data (out : ByteArray) (k : Key) :
    (k.push out).data.toList = out.data.toList ++ k.encode.data.toList := by
  cases k <;> simp only [Key.push, Key.encode, data_append] <;> rw [head_data out] <;> simp

mutual
/--
Writing an item onto a buffer appends the item's own encoding. Arrays and maps write their elements
one after another onto a shared buffer, and this is what lets each element's encoding be considered
alone.

`x.push out` writes `x` onto `out` and `x.push .empty` writes it alone; the equation says the first
is `out` followed by the second, for every item, by induction through arrays and maps.
-/
theorem push_data (out : ByteArray) : (x : Item) →
    (x.push out).data.toList = out.data.toList ++ (x.push .empty).data.toList
  | .uint n | .nint n => by simp only [Item.push]; rw [head_data]
  | .bytes b _ | .text b _ => by
    simp only [Item.push, data_append]; rw [head_data out]; simp
  | .array xs => by
    simp only [Item.push]
    rw [pushList_data _ xs, pushList_data (Head.push .empty _ _) xs, head_data out]
    simp
  | .map es => by
    simp only [Item.push]
    rw [pushEntries_data _ es, pushEntries_data (Head.push .empty _ _) es, head_data out]
    simp
  | .bool false | .bool true | .null => by simp only [Item.push]; rw [head_data]

/--
Writing a list of items onto a buffer appends their encodings. It is `push_data` for an array's
elements.

`Item.pushList out xs` writes the items of `xs` in order onto `out`; the equation says its bytes are
those of `out` followed by those of the same items written alone.
-/
theorem pushList_data (out : ByteArray) : (xs : List Item) →
    (Item.pushList out xs).data.toList = out.data.toList ++ (Item.pushList .empty xs).data.toList
  | [] => by simp [Item.pushList]
  | x :: xs => by
    simp only [Item.pushList]
    rw [pushList_data _ xs, pushList_data (x.push .empty) xs, push_data out x]
    simp

/--
Writing a list of map entries onto a buffer appends their encodings. It is `push_data` for a map's
entries, each a key then a value.

`Item.pushEntries out es` writes each key and value of `es` in order onto `out`; the equation says
its bytes are those of `out` followed by those of the same entries written alone.
-/
theorem pushEntries_data (out : ByteArray) : (es : List (Key × Item)) →
    (Item.pushEntries out es).data.toList =
      out.data.toList ++ (Item.pushEntries .empty es).data.toList
  | [] => by simp [Item.pushEntries]
  | (k, x) :: es => by
    simp only [Item.pushEntries]
    rw [pushEntries_data _ es, pushEntries_data (x.push (k.push .empty)) es,
      push_data (k.push out) x,
      push_data (k.push .empty) x, key_data out, key_data .empty]
    simp
end

/--
Bytes found at a position within the input end within the input, even when they are empty. The
decoder checks a byte string's length against the input before taking it, and an empty string has no
first byte to anchor `At.le_size`.

The hypotheses say `e` appears in `input` at `pos` and that `pos` is no further than the end; the
conclusion says `pos + e.length` is no further either.
-/
theorem At.le_size' {input : ByteArray} {pos : Nat} {e : List UInt8} (h : At input pos e)
    (hp : pos ≤ input.size) : pos + e.length ≤ input.size := by
  obtain ⟨r, h⟩ := h
  have := congrArg List.length h
  simp only [List.length_drop, List.length_append] at this
  rw [size_eq_length] at hp ⊢
  omega

/--
Asking for as many bytes as appear at a position succeeds, ending just past them. It is the step by
which byte strings and text are read once their head is.

With `bytes` at `p`, a declared length `n` equal to their length, and `p` within the input,
`Decode.readSlice` succeeds with the slice `input.extract p (p + n.toNat)` and the position after
it; `At.extract` says what that slice holds. `pos` and `hp` are the head's start and the proof it
precedes `p`, which the result type demands and nothing here constrains.
-/
theorem readSlice_ok {input : ByteArray} {pos p : Nat} {hp : pos < p} {n : UInt64}
    {bytes : List UInt8} (h : At input p bytes) (hn : n.toNat = bytes.length)
    (hsize : p ≤ input.size) :
    ∃ hb hq, Decode.readSlice input pos p hp n =
      .ok (⟨input.extract p (p + n.toNat), hb⟩, ⟨p + n.toNat, hq⟩) := by
  have hle := h.le_size' hsize
  unfold Decode.readSlice
  rw [dite_eq_left (by omega)]
  exact ⟨_, _, rfl⟩

/--
Decoding a string's own bytes as UTF-8 gives back the string. It is the fact on which text survives
the round trip unchanged.

For any byte array `b` with a proof that it is valid UTF-8, if `b` is the bytes of `s` then
`String.fromUTF8 b hv` is `s`; the proof of validity plays no part in the result.
-/
theorem fromUTF8_eq {s : String} : ∀ (b : ByteArray) (hv : b.IsValidUTF8),
    b = s.toByteArray → String.fromUTF8 b hv = s := by
  rintro _ _ rfl; rfl

/--
Reading the UTF-8 bytes of a string at a position gives back the string. It is the text round trip
once the head has been read.

With the bytes of `s` at `p`, a declared length equal to their count, and `p` within the input,
`Decode.readText` succeeds with `s` and the position just past its bytes. The bound proof it returns
is the one a `Value` needs.
-/
theorem readText_ok {input : ByteArray} {pos p : Nat} {hp : pos < p} {n : UInt64} {s : String}
    (h : At input p s.toUTF8.data.toList) (hn : n.toNat = s.utf8ByteSize)
    (hsize : p ≤ input.size) :
    ∃ hs hq, Decode.readText input pos p hp n = .ok (⟨s, hs⟩, ⟨p + n.toNat, hq⟩) := by
  have hlen : n.toNat = s.toUTF8.data.toList.length := by
    rw [hn, ← size_eq_length]; simp
  obtain ⟨hb, hq, hr⟩ := readSlice_ok (hp := hp) h hlen hsize
  have hext : input.extract p (p + n.toNat) = s.toByteArray := by
    apply bytes_ext; rw [hlen, h.extract]; simp
  unfold Decode.readText
  rw [hr]
  simp only
  rw [dite_eq_left (hext ▸ s.isValidUTF8)]
  refine ⟨by have := n.toNat_lt; omega, hq, ?_⟩
  simp only [Except.ok.injEq, Prod.mk.injEq, and_true]
  exact Subtype.ext (fromUTF8_eq _ _ hext)

/--
Any key the encoder writes is read back exactly by the decoder's key reader. Map keys are read by
their own path, which refuses anything that is not an integer or text, and this shows that path
accepts every key the encoder can emit.

With `k.encode` at `pos`, `Decode.readKey` succeeds with `k` itself and the position just past its
encoding.
-/
theorem readKey_ok {input : ByteArray} {pos : Nat} (k : Key)
    (h : At input pos k.encode.data.toList) :
    ∃ hq, Decode.readKey input pos = .ok (k, ⟨pos + k.encode.size, hq⟩) := by
  cases k with
  | uint n =>
    obtain ⟨hp, hr⟩ := readHead_push (major := 0) (by omega) n.toNat_lt h
    refine ⟨hp, ?_⟩
    unfold Decode.readKey
    rw [hr]
    simp [Decode.Head.ofMajor, Key.encode, Key.push, Head.unsigned]
  | nint n =>
    obtain ⟨hp, hr⟩ := readHead_push (major := 1) (by omega) n.toNat_lt h
    refine ⟨hp, ?_⟩
    unfold Decode.readKey
    rw [hr]
    simp [Decode.Head.ofMajor, Key.encode, Key.push, Head.negative]
  | text s hs =>
    have h' : At input pos ((Head.push .empty Head.textString s.utf8ByteSize).data.toList ++
        s.toUTF8.data.toList) := by
      simpa [Key.encode, Key.push, data_append] using h
    obtain ⟨hp, hr⟩ := readHead_push (major := 3) (by omega) hs h'.left
    have hat := h'.right
    rw [← size_eq_length] at hat
    obtain ⟨_, hq, ht⟩ := readText_ok (pos := pos) (hp := hp.1)
      (n := UInt64.ofNat s.utf8ByteSize)
      hat (UInt64.toNat_ofNat_of_lt' hs) hp.2
    have hend : pos + (Head.push .empty 3 s.utf8ByteSize).size +
        (UInt64.ofNat s.utf8ByteSize).toNat =
        pos + (Key.text s hs).encode.size := by
      simp [Key.encode, Key.push, Head.textString, ByteArray.size_append,
        UInt64.toNat_ofNat_of_lt' hs, Nat.add_assoc]
    refine ⟨hend ▸ hq, ?_⟩
    unfold Decode.readKey
    rw [hr]
    simp only [Decode.Head.ofMajor]
    simp only [show (3 == 0) = false from rfl, show (3 == 1) = false from rfl,
      show (3 == 2) = false from rfl, show (3 == 3) = true from rfl, Bool.false_eq_true,
      ↓reduceIte]
    rw [ht]
    simp only [Except.ok.injEq, Prod.mk.injEq, Subtype.mk.injEq, true_and]
    exact hend

end Tests.Proofs
