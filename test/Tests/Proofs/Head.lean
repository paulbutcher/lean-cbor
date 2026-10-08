/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Tests.Proofs.Bytes

@[expose] public section

namespace Tests.Proofs
open Cbor

def be (n : Nat) : Nat → List UInt8
  | 0 => []
  | k + 1 => UInt8.ofNat (n / 256 ^ k) :: be n k

/--
The big-endian spelling of a number in `k` bytes has exactly `k` bytes. Heads are measured by their
length, and this fixes the length of the argument part.

`be n k` is the list of bytes `Head.pushBigEndian` writes for `n` in `k` bytes; its length is `k`
whatever `n` is, including when `n` needs more bytes than `k`, since only the low `k` are written.
-/
theorem length_be (n k : Nat) : (be n k).length = k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [be, ih]

/--
`Head.pushBigEndian` appends the bytes `be` describes. It turns the encoder's loop over a buffer
into a list the proofs can compute with.

`Head.pushBigEndian out n k` writes the low `k` bytes of `n` onto `out`; the equation says its bytes
are those of `out` followed by `be n k`, for every buffer, number and width.
-/
theorem pushBigEndian_data (out : ByteArray) (n k : Nat) :
    (Head.pushBigEndian out n k).data.toList = out.data.toList ++ be n k := by
  induction k generalizing out with
  | zero => simp [Head.pushBigEndian, be]
  | succ k ih => simp [Head.pushBigEndian, be, ih]

/--
Reading the big-endian bytes of `n` back with an accumulator gives the accumulator shifted past them
plus `n` modulo the width. This is the arithmetic heart of the head round trip, stated with the
accumulator free so that induction on the width goes through.

The left side is the fold `Decode.bigEndian` performs, started from `acc` and run over the `k` bytes
`be n k`. The right side is `acc` shifted left by `k` bytes plus the low `k` bytes of `n`, which is
what reading those bytes as a big-endian number must give.
-/
theorem foldl_be (n k acc : Nat) :
    (be n k).foldl (fun acc b => acc * 256 + b.toNat) acc = acc * 256 ^ k + n % 256 ^ k := by
  induction k generalizing acc with
  | zero => simp [be, Nat.mod_one]
  | succ k ih =>
    rw [Nat.mod_pow_succ]
    simp only [be, List.foldl_cons, ih, UInt8.toNat_ofNat']
    simp only [Nat.pow_succ]
    generalize 256 ^ k = X
    generalize n / X % 256 = d
    generalize n % X = m
    simp only [Nat.add_mul, Nat.mul_assoc, Nat.mul_comm 256 X, Nat.mul_comm d X]
    omega

/--
A number that fits in `k` bytes, written in `k` bytes and read back, is itself. It is the head round
trip for the argument once the width has been chosen.

`Decode.bigEndian (be n k)` is the decoder reading the `k` bytes the encoder wrote for `n`; the
hypothesis `n < 256 ^ k` says `n` fits, and the equation says the decoder recovers `n` exactly.
-/
theorem bigEndian_be {n k : Nat} (h : n < 256 ^ k) : Decode.bigEndian (be n k) = n := by
  simp [Decode.bigEndian, foldl_be, Nat.mod_eq_of_lt h]

/--
The initial byte for a major type and additional information has the numeric value the decoder takes
apart. The decoder recovers both fields by division and remainder, and this is what they divide.

`Head.initial major info` is the byte the encoder writes; with `major < 8` and `info < 32` both fit
their fields, and the equation says the byte's value is `major * 32 + info`. Outside those bounds
the byte would wrap, which is why they are hypotheses.
-/
theorem initial_toNat {major info : Nat} (hm : major < 8) (hi : info < 32) :
    (Head.initial major info).toNat = major * 32 + info := by
  simp [Head.initial, UInt8.toNat_ofNat']
  omega

/--
A head whose argument is below 24, written as the single byte the encoder emits, is read back as
that major type and argument, ending one byte later. This is the head round trip for the short form.

The hypotheses fix a major type from 0 to 5, an argument below 24, and say the initial byte appears
at `pos`. The conclusion says `Decode.readHead` returns the head `Head.ofMajor` builds for that
major type and argument, with `pos + 1` as the position after it.
-/
theorem readHead_short {major n : Nat} (hm : major ≤ 5) (hn : n < 24) {input : ByteArray}
    {pos : Nat} (h : At input pos [Head.initial major n]) :
    ∃ hp, Decode.readHead input pos =
      .ok (Decode.Head.ofMajor major (UInt64.ofNat n), ⟨pos + 1, hp⟩) := by
  obtain ⟨hp, hx⟩ := h.getElem
  have hv : input[pos].toNat = major * 32 + n := by
    rw [hx]; exact initial_toNat (by omega) (by omega)
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  unfold Decode.readHead
  rw [dif_pos hp]
  have h1 : (major * 32 + n) / 32 = major := by omega
  have h2 : (major * 32 + n) % 32 = n := by omega
  simp only [hv, h1, h2]
  repeat' split
  all_goals first | omega | simp_all

/--
A head whose argument needs 1, 2, 4 or 8 further bytes, written as the encoder writes it, is read
back as that major type and argument. It covers the four long forms at once, parameterised by the
width and the least argument that width is allowed to hold.

`Decode.argumentForm info = (width, least)` ties the additional information to its width and its
minimum; `least ≤ n` says the argument is not one a shorter head would hold, which is what the
decoder's minimality check demands, and `n < 256 ^ width` says it fits. With the initial byte and
the `width` big-endian bytes at `pos`, `Decode.readHead` returns the head for `major` and `n`,
ending at `pos + 1 + width`.
-/
theorem readHead_wide {major n info width least : Nat} (hm : major ≤ 5)
    (hform : Decode.argumentForm info = (width, least)) (hi : 24 ≤ info ∧ info ≤ 27)
    (hleast : least ≤ n) (hn : n < 256 ^ width) {input : ByteArray} {pos : Nat}
    (h : At input pos (Head.initial major info :: be n width)) :
    ∃ hp, Decode.readHead input pos =
      .ok (Decode.Head.ofMajor major (UInt64.ofNat n), ⟨pos + 1 + width, hp⟩) := by
  obtain ⟨hp, hx⟩ := h.getElem
  have hv : input[pos].toNat = major * 32 + info := by
    rw [hx]; exact initial_toNat (by omega) (by omega)
  have hle := h.le_size
  simp only [List.length_cons, length_be] at hle
  have hext : (input.extract (pos + 1) (pos + 1 + width)).data.toList = be n width := by
    have := (show At input pos ([Head.initial major info] ++ be n width) from h).right.extract
    simpa [length_be] using this
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  unfold Decode.readHead
  rw [dif_pos hp]
  have h1 : (major * 32 + info) / 32 = major := by omega
  have h2 : (major * 32 + info) % 32 = info := by omega
  simp only [hv, h1, h2, hform, hext, bigEndian_be hn]
  repeat' split
  all_goals first | omega | simp_all

/--
Writing a head onto a buffer appends the head's own encoding. It separates where an encoding is
written from what it is, which every later proof relies on.

`Head.push out major n` is the encoder writing a head onto `out`, and `Head.push .empty major n` is
the same head written alone; the equation says the first is `out` followed by the second.
-/
theorem head_data (out : ByteArray) (major n : Nat) :
    (Head.push out major n).data.toList =
      out.data.toList ++ (Head.push .empty major n).data.toList := by
  unfold Head.push
  repeat' split
  all_goals simp [pushBigEndian_data]

/--
A decoding result can be restated with the position it ends at written another way. Positions arrive
as sums assembled in different orders, and this saves restating each result by hand.

The hypothesis says `e` succeeds with `x` and a position `a` that carries some proof; given `a = b`,
the conclusion says it succeeds with `x` at `b`. The proof carried along is only what the result
type demands, so changing its expression changes nothing.
-/
theorem ok_at {α : Type} {P : Nat → Prop} {e : Except Error (α × {p : Nat // P p})} {x : α}
    {a b : Nat} (hab : a = b) (h : ∃ hp, e = .ok (x, ⟨a, hp⟩)) :
    ∃ hp, e = .ok (x, ⟨b, hp⟩) := by
  subst hab; exact h

/--
`ok_at` for `Decode.readHead`, whose position type the general form cannot infer. It is the same
restatement, made usable where the head is read.

Given `a = b` and a successful read of head `H` ending at `a`, the conclusion is the same read
ending at `b`.
-/
theorem readHead_at {input : ByteArray} {pos a b : Nat} {H : Decode.Head} (hab : a = b)
    (hr : ∃ hp, Decode.readHead input pos = .ok (H, ⟨a, hp⟩)) :
    ∃ hp, Decode.readHead input pos = .ok (H, ⟨b, hp⟩) := by
  subst hab; exact hr

/--
Any head the encoder writes for an argument that fits 64 bits is read back exactly by the decoder.
It is the head round trip in full, the base on which every item's round trip is built.

`Head.push .empty major n` is the head the encoder writes; `major ≤ 5` restricts it to the major
types whose argument is a number or a length, and `n < 2 ^ 64` is the range a head can hold. With
those bytes at `pos`, `Decode.readHead` returns `Head.ofMajor major (UInt64.ofNat n)`, which is that
major type with `n` as its argument, and the position just after the head.
-/
theorem readHead_push {major n : Nat} (hm : major ≤ 5) (hn : n < 2 ^ 64) {input : ByteArray}
    {pos : Nat} (h : At input pos (Head.push .empty major n).data.toList) :
    ∃ hp, Decode.readHead input pos =
      .ok (Decode.Head.ofMajor major (UInt64.ofNat n),
        ⟨pos + (Head.push .empty major n).size, hp⟩) := by
  rw [size_eq_length]
  unfold Head.push at h ⊢
  by_cases h0 : n < 24
  · simp only [h0, ↓reduceIte, data_push] at h ⊢
    exact readHead_at (by simp) (readHead_short hm h0 (by simpa using h))
  by_cases h1 : n < 0x100
  · simp only [h0, h1, ↓reduceIte, pushBigEndian_data, data_push] at h ⊢
    exact readHead_at (by simp [length_be])
      (readHead_wide (info := 24) (width := 1) (least := 24)
        hm (by rfl) (by omega) (by omega) (by omega) (by simpa using h))
  by_cases h2 : n < 0x10000
  · simp only [h0, h1, h2, ↓reduceIte, pushBigEndian_data, data_push] at h ⊢
    exact readHead_at (by simp [length_be])
      (readHead_wide (info := 25) (width := 2) (least := 0x100)
        hm (by rfl) (by omega) (by omega) (by omega) (by simpa using h))
  by_cases h3 : n < 0x100000000
  · simp only [h0, h1, h2, h3, ↓reduceIte, pushBigEndian_data, data_push] at h ⊢
    exact readHead_at (by simp [length_be])
      (readHead_wide (info := 26) (width := 4) (least := 0x10000)
        hm (by rfl) (by omega) (by omega) (by omega) (by simpa using h))
  · simp only [h0, h1, h2, h3, ↓reduceIte, pushBigEndian_data, data_push] at h ⊢
    exact readHead_at (by simp [length_be])
      (readHead_wide (info := 27) (width := 8) (least := 0x100000000)
        hm (by rfl) (by omega) (by omega) (by omega) (by simpa using h))
