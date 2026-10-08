/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cbor

@[expose] public section

namespace Tests.Proofs
open Cbor

def At (input : ByteArray) (pos : Nat) (e : List UInt8) : Prop :=
  ∃ rest, input.data.toList.drop pos = e ++ rest

/--
Pushing a byte onto a byte array appends it to the array's list of bytes. The proofs reason about
encodings as lists, where append has a rich theory, and this is the bridge from the `ByteArray`
operation the encoder performs.

`(b.push x).data.toList` is the bytes of `b` after pushing `x`; the right side is the bytes of `b`
with `x` on the end. The equation holds for every array and byte.
-/
theorem data_push (b : ByteArray) (x : UInt8) :
    (b.push x).data.toList = b.data.toList ++ [x] := by
  simp [ByteArray.data_push]

/--
Appending byte arrays appends their lists of bytes. Like `data_push`, it lets the proofs move from
the encoder's `ByteArray` operations to list reasoning.

`(a ++ b).data.toList` is the bytes of the concatenation, and the right side concatenates the two
lists of bytes; the equation holds for every pair of arrays.
-/
theorem data_append (a b : ByteArray) :
    (a ++ b).data.toList = a.data.toList ++ b.data.toList := by
  simp [ByteArray.data_append]

/--
A byte array's size is the length of its list of bytes. The decoder measures positions by `size` and
the proofs measure encodings by list length, so every comparison between the two passes through
this.

`b.size` is what the decoder compares positions against, and `b.data.toList.length` is the length
the list lemmas speak of; the equation says they are the same number for every array.
-/
theorem size_eq_length (b : ByteArray) : b.size = b.data.toList.length :=
  Array.length_toList.symm

/--
Bytes found at a position include any prefix of them found at that position. This is how a proof
about a head, which is the front of an item's encoding, is extracted from the fact that the whole
encoding is present.

`At input pos (a ++ b)` answers `true` when `a ++ b` appears in `input` starting at `pos`; the
conclusion says `a` appears there too.
-/
theorem At.left {input : ByteArray} {pos : Nat} {a b : List UInt8} (h : At input pos (a ++ b)) :
    At input pos a := by
  obtain ⟨r, h⟩ := h
  exact ⟨b ++ r, by simp [h]⟩

/--
Bytes found at a position have their suffix found further along by the length of the prefix. This is
how a proof steps from one item's encoding to the next.

The hypothesis says `a ++ b` appears in `input` at `pos`; the conclusion says `b` appears at `pos +
a.length`, which is where the decoder resumes once it has read `a`.
-/
theorem At.right {input : ByteArray} {pos : Nat} {a b : List UInt8} (h : At input pos (a ++ b)) :
    At input (pos + a.length) b := by
  obtain ⟨r, h⟩ := h
  refine ⟨r, ?_⟩
  rw [← List.drop_drop, h]
  simp

/--
When bytes beginning with `x` appear at a position, the input holds `x` at that position, and the
position is in range. The decoder's first act on any item is to read that byte, and this is what
tells the proof what it reads.

The hypothesis says `x :: e` appears in `input` at `pos`. The conclusion gives a proof that `pos <
input.size`, which is what the decoder's bounds check asks, and says `input[pos]`, the byte it
reads, is `x`.
-/
theorem At.getElem {input : ByteArray} {pos : Nat} {x : UInt8} {e : List UInt8}
    (h : At input pos (x :: e)) : ∃ hp : pos < input.size, input[pos] = x := by
  obtain ⟨r, h⟩ := h
  have hlen : pos < input.data.toList.length := by
    have := congrArg List.length h
    simp only [List.length_drop, List.length_append, List.length_cons] at this
    omega
  have hp : pos < input.size := by rw [size_eq_length]; exact hlen
  refine ⟨hp, ?_⟩
  have := congrArg (·[0]?) h
  simp at this
  rw [Array.getElem?_eq_getElem hp] at this
  simpa [ByteArray.getElem_eq_getElem_data] using this

/--
Nonempty bytes found at a position end within the input. The decoder refuses an item whose bytes
would run past the end, and this is what shows a present encoding does not.

The hypothesis says `x :: e` appears in `input` at `pos`; the conclusion says that position plus the
length of those bytes is at most `input.size`. The bytes are nonempty because a position past the
end has only the empty list at it, so the claim would fail for `[]`.
-/
theorem At.le_size {input : ByteArray} {pos : Nat} {x : UInt8} {e : List UInt8}
    (h : At input pos (x :: e)) : pos + (x :: e).length ≤ input.size := by
  obtain ⟨r, h⟩ := h
  have := congrArg List.length h
  simp at this
  rw [size_eq_length]
  simp
  omega

/--
Extracting from a position as many bytes as were found there gives back exactly those bytes. The
decoder takes byte strings, text and key encodings by `extract`, and this says what it gets.

The hypothesis says `e` appears in `input` at `pos`; the conclusion says the bytes of `input.extract
pos (pos + e.length)`, the slice the decoder would take, are `e`.
-/
theorem At.extract {input : ByteArray} {pos : Nat} {e : List UInt8} (h : At input pos e) :
    (input.extract pos (pos + e.length)).data.toList = e := by
  obtain ⟨r, h⟩ := h
  simp [ByteArray.data_extract, List.extract_eq_take_drop, h]

end Tests.Proofs
