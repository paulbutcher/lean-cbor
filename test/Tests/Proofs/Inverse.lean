/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Tests.Proofs.Theorems

@[expose] public section

namespace Tests.Proofs
open Cbor

/--
A slice of a byte array, as a list, is the input's list with the front dropped and the rest cut to
length. The inverse proofs reason about what the decoder read in list terms, and this is how its
slices get there.

`input.extract a b` is the slice from `a` to `b`; the right side drops `a` bytes from `input`'s list
and keeps the next `b - a`. The equation holds for all positions, including ones past the end, where
both sides are short in the same way.
-/
theorem extract_data (input : ByteArray) (a b : Nat) :
    (input.extract a b).data.toList = (input.data.toList.drop a).take (b - a) := by
  simp [ByteArray.data_extract, List.extract_eq_take_drop]

/--
Reading big-endian bytes from a nonzero accumulator is the accumulator shifted past them plus
reading them from zero. It is what lets the value of a list of bytes be split at its first byte.

The left side is `Decode.bigEndian`'s fold started from `acc`; the right side shifts `acc` left by
one byte per element of `l` and adds the fold started from zero. The equation holds for every list
and accumulator.
-/
theorem foldl_acc (l : List UInt8) (acc : Nat) :
    l.foldl (fun acc b => acc * 256 + b.toNat) acc =
      acc * 256 ^ l.length + l.foldl (fun acc b => acc * 256 + b.toNat) 0 := by
  induction l generalizing acc with
  | nil => simp
  | cons b l ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [ih, ih (0 * 256 + b.toNat), Nat.pow_succ]
    generalize 256 ^ l.length = X
    generalize l.foldl (fun acc b => acc * 256 + b.toNat) 0 = m
    simp only [Nat.zero_mul, Nat.zero_add, Nat.add_mul, Nat.mul_assoc, Nat.mul_comm 256 X]
    omega

/--
A number read from `k` big-endian bytes is less than `256 ^ k`. It is the bound that shows a decoded
argument fits 64 bits and that writing it back takes the same width.

`Decode.bigEndian l` is the decoder's reading of `l`, and `256 ^ l.length` the first number too
large for that many bytes; the inequality holds for every list.
-/
theorem bigEndian_lt (l : List UInt8) : Decode.bigEndian l < 256 ^ l.length := by
  induction l with
  | nil => simp [Decode.bigEndian]
  | cons b l ih =>
    simp only [Decode.bigEndian, List.foldl_cons, List.length_cons] at ih ⊢
    rw [foldl_acc, Nat.pow_succ]
    have hb := b.toNat_lt
    simp only [Nat.zero_mul, Nat.zero_add]
    generalize 256 ^ l.length = X at ih ⊢
    have : b.toNat * X + X ≤ 256 * X := by
      have := Nat.mul_le_mul_right X (show b.toNat + 1 ≤ 256 by omega)
      simpa [Nat.add_mul] using this
    rw [Nat.mul_comm X 256]
    omega

/--
Two numbers equal modulo 256 become the same byte. Bytes are written with `UInt8.ofNat`, which
wraps, and this is the form in which two writes are compared.

The hypothesis says `a` and `b` agree in their low eight bits; the conclusion says `UInt8.ofNat`
gives the same byte for both.
-/
theorem ofNat_eq_ofNat {a b : Nat} (h : a % 256 = b % 256) : UInt8.ofNat a = UInt8.ofNat b :=
  UInt8.toNat_inj.mp (by simp [UInt8.toNat_ofNat']; omega)

/--
Writing a number in `k` big-endian bytes depends only on its low `k` bytes. It is what lets the
inverse proof discard the leading byte once it has been accounted for.

`be n k` is the encoder's spelling of `n` in `k` bytes and `be (n % 256 ^ k) k` the spelling of its
low `k` bytes; the equation says they are the same list.
-/
theorem be_mod (n k : Nat) : be n k = be (n % 256 ^ k) k := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih =>
    simp only [be]
    congr 1
    · apply ofNat_eq_ofNat
      rw [Nat.pow_succ, Nat.mod_mul_right_div_self]
      simp
    · rw [ih n, ih (n % 256 ^ (k + 1)),
        Nat.mod_mod_of_dvd n (Nat.pow_dvd_pow 256 (Nat.le_succ k))]

/--
Reading bytes as a big-endian number and writing that number back in as many bytes gives the same
bytes. It is the inverse of `bigEndian_be`, and what shows a head's argument bytes are reproduced
exactly.

`Decode.bigEndian l` is what the decoder reads from `l`, and `be _ l.length` writes it back at the
same width; the equation says the result is `l` for every list.
-/
theorem be_bigEndian (l : List UInt8) : be (Decode.bigEndian l) l.length = l := by
  induction l with
  | nil => rfl
  | cons b t ih =>
    have ht := bigEndian_lt t
    have hX : 0 < 256 ^ t.length := Nat.pow_pos (by omega)
    have hN : Decode.bigEndian (b :: t) = b.toNat * 256 ^ t.length + Decode.bigEndian t := by
      simp only [Decode.bigEndian, List.foldl_cons]
      rw [foldl_acc]
      simp
    simp only [List.length_cons, be]
    rw [hN]
    congr 1
    · rw [Nat.add_comm, Nat.add_mul_div_right _ _ hX, Nat.div_eq_of_lt ht, Nat.zero_add]
      exact UInt8.ofNat_toNat
    · rw [be_mod, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ht, ih]

/-- The bytes the encoder writes for a head. -/
def headEncode : Decode.Head → ByteArray
  | .uint n => Head.push .empty 0 n.toNat
  | .nint n => Head.push .empty 1 n.toNat
  | .bytes n => Head.push .empty 2 n.toNat
  | .text n => Head.push .empty 3 n.toNat
  | .array n => Head.push .empty 4 n.toNat
  | .map n => Head.push .empty 5 n.toNat
  | .simple v => v.item.push .empty

/--
The encoding of a head built by `Decode.Head.ofMajor` is the encoder's head for that major type and
argument. It joins the decoder's representation of a head to the bytes the encoder writes for it.

`headEncode` is the bytes the encoder writes for a decoded head; for a major type from 0 to 5 and
argument `n`, they are `Head.push .empty major n.toNat`. The bound on `major` matters because
`ofMajor` maps every larger value to a map.
-/
theorem ofMajor_encode {major : Nat} (hm : major ≤ 5) (n : UInt64) :
    headEncode (Decode.Head.ofMajor major n) = Head.push .empty major n.toNat := by
  rcases (by omega :
      major = 0 ∨ major = 1 ∨ major = 2 ∨ major = 3 ∨ major = 4 ∨ major = 5)
    with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/--
The encoder writes an argument in exactly the width the decoder accepted it at. A decoded argument
is at least the least value its width allows and less than the next, which is precisely the range in
which the encoder chooses that width.

The hypotheses fix the additional information from 24 to 27, the width and least value
`Decode.argumentForm` gives it, and an argument `n` from `least` to below `256 ^ width`. The
conclusion says `Head.push` writes the initial byte with that additional information followed by `n`
in `width` bytes.
-/
theorem head_push_wide {major info width least n : Nat} (hi : 24 ≤ info ∧ info ≤ 27)
    (hform : Decode.argumentForm info = (width, least)) (hl : least ≤ n) (hn : n < 256 ^ width) :
    (Head.push .empty major n).data.toList = Head.initial major info :: be n width := by
  rcases (by omega : info = 24 ∨ info = 25 ∨ info = 26 ∨ info = 27) with rfl | rfl | rfl | rfl
  all_goals
    simp only [Decode.argumentForm] at hform
    obtain ⟨rfl, rfl⟩ := hform
    unfold Head.push
    simp at hl hn
    repeat' split
    all_goals first | omega | simp [pushBigEndian_data]

/--
A one-byte slice holds the byte at its position. The decoder reads the initial byte of a head by
index, and this relates that to the slice the inverse proofs speak of.

With `pos` within `input`, the slice from `pos` to `pos + 1` is the single byte `input[pos]`.
-/
theorem extract_one {input : ByteArray} {pos : Nat} (h : pos < input.size) :
    (input.extract pos (pos + 1)).data.toList = [input[pos]] := by
  rw [extract_data, Nat.add_sub_cancel_left]
  rw [List.drop_eq_getElem_cons (by rw [← size_eq_length]; exact h)]
  simp [ByteArray.getElem_eq_getElem_data]

/--
A slice beginning within the input is its first byte followed by the rest. It is how a head's
initial byte is separated from the argument bytes after it.

With `pos` within `input` and before `e`, the slice from `pos` to `e` is `input[pos]` followed by
the slice from `pos + 1` to `e`.
-/
theorem extract_cons {input : ByteArray} {pos e : Nat} (h : pos < input.size) (he : pos < e) :
    (input.extract pos e).data.toList = input[pos] :: (input.extract (pos + 1) e).data.toList := by
  rw [extract_data, extract_data,
    List.drop_eq_getElem_cons (by rw [← size_eq_length]; exact h)]
  rw [show e - pos = (e - (pos + 1)) + 1 by omega, List.take_succ_cons]
  simp [ByteArray.getElem_eq_getElem_data]

/--
Whatever head the decoder accepts, the encoder writes back byte for byte. Non-minimal heads are
refused, which is what makes this hold: every accepted head is the one the encoder would choose.

The hypothesis says `Decode.readHead` succeeded at `pos` with head `H`, ending at `p`. The
conclusion says the bytes from `pos` to `p` are `headEncode H`, the encoder's bytes for that head.
-/
theorem readHead_inv {input : ByteArray} {pos p : Nat} {H : Decode.Head} {hp}
    (h : Decode.readHead input pos = .ok (H, ⟨p, hp⟩)) :
    (input.extract pos p).data.toList = (headEncode H).data.toList := by
  unfold Decode.readHead at h
  split at h
  case isFalse => simp at h
  case isTrue hpos =>
  have hlt := input[pos].toNat_lt
  have hbv : input[pos] = Head.initial (input[pos].toNat / 32) (input[pos].toNat % 32) :=
    UInt8.toNat_inj.mp (by rw [initial_toNat (by omega) (by omega)]; omega)
  dsimp only at h
  generalize hB : input[pos] = B at h hbv hlt
  repeat' split at h
  all_goals first | (simp at h; done) | skip
  all_goals
    simp only [Except.ok.injEq, Prod.mk.injEq, Subtype.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [beq_iff_eq] at *
  · rename_i e1 e2
    rw [extract_one hpos, hB, hbv, e1, e2]
    simp [headEncode, Value.bool, Item.push, Head.push, Head.simple, Head.falseValue]
  · rename_i e1 _ e2
    rw [extract_one hpos, hB, hbv, e1, e2]
    simp [headEncode, Value.bool, Item.push, Head.push, Head.simple, Head.trueValue]
  · rename_i e1 _ _ e2
    rw [extract_one hpos, hB, hbv, e1, e2]
    simp [headEncode, Value.null, Item.push, Head.push, Head.simple, Head.nullValue]
  · rw [extract_one hpos, hB, ofMajor_encode (by omega)]
    have hi : (UInt64.ofNat (B.toNat % 32)).toNat = B.toNat % 32 :=
      UInt64.toNat_ofNat_of_lt' (by simp [UInt64.size]; omega)
    rw [hi]
    conv => lhs; rw [hbv]
    unfold Head.push
    rw [if_pos (by omega)]
    simp
  · have hi : 24 ≤ B.toNat % 32 ∧ B.toNat % 32 ≤ 27 := by omega
    generalize hform : Decode.argumentForm (B.toNat % 32) = form at *
    obtain ⟨width, least⟩ := form
    simp only at *
    have hwidth : width ≤ 8 := by
      rcases (by omega : B.toNat % 32 = 24 ∨ B.toNat % 32 = 25 ∨ B.toNat % 32 = 26 ∨
        B.toNat % 32 = 27) with h | h | h | h <;>
        simp [h, Decode.argumentForm] at hform <;> omega
    have hslice : (input.extract (pos + 1) (pos + 1 + width)).data.toList.length = width := by
      rw [← size_eq_length, ByteArray.size_extract]; omega
    generalize hS : (input.extract (pos + 1) (pos + 1 + width)).data.toList = S at *
    have hlt' := bigEndian_lt S
    rw [hslice] at hlt'
    have h64 : 256 ^ width ≤ 2 ^ 64 := by
      calc 256 ^ width ≤ 256 ^ 8 := Nat.pow_le_pow_right (by omega) hwidth
        _ = 2 ^ 64 := rfl
    rw [ofMajor_encode (by omega), UInt64.toNat_ofNat_of_lt' (by simp [UInt64.size]; omega),
      head_push_wide hi hform (by omega) hlt', ← hslice, be_bigEndian]
    rw [extract_cons hpos (by omega), hB, hslice, hS]
    exact congrArg (· :: S) hbv

/--
Adjacent slices join into the slice spanning both. The inverse proofs build an item's bytes piece by
piece and need to recognise the whole.

With `a ≤ b ≤ c`, the slice from `a` to `c` is the slice from `a` to `b` followed by the slice
from `b` to `c`.
-/
theorem extract_split (input : ByteArray) {a b c : Nat} (hab : a ≤ b) (hbc : b ≤ c) :
    (input.extract a c).data.toList =
      (input.extract a b).data.toList ++ (input.extract b c).data.toList := by
  rw [← data_append, ByteArray.extract_append_extract, Nat.min_eq_left hab, Nat.max_eq_right hbc]

/--
A slice the decoder takes is exactly the bytes it spans, and ends where the declared length says. It
is the inverse of `readSlice_ok`.

The hypothesis says `Decode.readSlice` succeeded with bytes `b` and end `q`; the conclusion says `b`
is the input from `p` to `q` and `q` is `p` plus the declared length.
-/
theorem readSlice_inv {input : ByteArray} {pos p : Nat} {hp : pos < p} {n : UInt64}
    {b : ByteArray} {hb} {q : Nat} {hq}
    (h : Decode.readSlice input pos p hp n = .ok (⟨b, hb⟩, ⟨q, hq⟩)) :
    b = input.extract p q ∧ q = p + n.toNat := by
  unfold Decode.readSlice at h
  split at h
  · simp only [Except.ok.injEq, Prod.mk.injEq, Subtype.mk.injEq] at h
    obtain ⟨h1, rfl⟩ := h
    exact ⟨h1.symm, rfl⟩
  · simp at h

/--
Text the decoder accepts has, as its UTF-8, exactly the bytes it was read from. It is the inverse of
`readText_ok`, and holds because invalid UTF-8 is refused rather than repaired.

The hypothesis says `Decode.readText` succeeded with string `s` and end `q`; the conclusion says
`s.toUTF8` is the input from `p` to `q` and `q` is `p` plus the declared length.
-/
theorem readText_inv {input : ByteArray} {pos p : Nat} {hp : pos < p} {n : UInt64}
    {s : String} {hs} {q : Nat} {hq}
    (h : Decode.readText input pos p hp n = .ok (⟨s, hs⟩, ⟨q, hq⟩)) :
    s.toUTF8 = input.extract p q ∧ q = p + n.toNat := by
  unfold Decode.readText at h
  split at h
  · simp at h
  · rename_i b hb q' hr
    split at h
    · simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨h1, rfl⟩ := h
      have h2 := congrArg Subtype.val h1
      simp only at h2
      subst h2
      obtain ⟨rfl, rfl⟩ := readSlice_inv hr
      exact ⟨by simp [String.toUTF8_eq_toByteArray, String.fromUTF8], rfl⟩
    · simp at h

/--
A key the decoder accepts encodes to exactly the bytes it was read from. The decoder compares keys
by those bytes, and the encoder sorts them by their encodings, so this is what makes the two orders
the same order.

The hypothesis says `Decode.readKey` succeeded at `pos` with key `k`, ending at `q`; the conclusion
says `k.encode` is the input from `pos` to `q`.
-/
theorem readKey_inv {input : ByteArray} {pos : Nat} {k : Key} {q : Nat} {hq}
    (h : Decode.readKey input pos = .ok (k, ⟨q, hq⟩)) :
    k.encode.data.toList = (input.extract pos q).data.toList := by
  unfold Decode.readKey at h
  split at h
  · simp at h
  · rename_i n p hr
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rw [readHead_inv hr]
    rfl
  · rename_i n p hr
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rw [readHead_inv hr]
    rfl
  · rename_i n p hr
    split at h
    · simp at h
    · rename_i s hs q' ht
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨hs', rfl⟩ := readText_inv ht
      obtain ⟨p, hp⟩ := p
      simp only at hq hs'
      have hlen : s.utf8ByteSize = n.toNat := by
        have := congrArg ByteArray.size hs'
        rw [ByteArray.size_extract, Nat.min_eq_left hq.2] at this
        simp at this
        omega
      rw [extract_split input (Nat.le_of_lt hp.1) (Nat.le_add_right _ _), readHead_inv hr,
        ← hs']
      simp [Key.encode, Key.push, headEncode, Head.textString, hlen]
  · simp at h

/--
When the decoder's order check passes, the previous key's encoding precedes the current one
strictly. It is what the decoder's acceptance of a map says about the order of its keys.

The hypothesis says `Decode.checkOrder` accepted `current` after `previous`; the conclusion says
that for the previous encoding, if there is one, `Order.compareEncoded` puts it strictly before
`current`.
-/
theorem checkOrder_inv {previous : Option ByteArray} {current : ByteArray} {pos : Nat}
    (h : Decode.checkOrder previous current pos = .ok ()) :
    ∀ p ∈ previous, Order.compareEncoded p current = .lt := by
  intro p hp
  cases previous with
  | none => simp at hp
  | some p' =>
    simp only [Option.mem_def, Option.some.injEq] at hp
    subst hp
    unfold Decode.checkOrder at h
    repeat' split at h
    all_goals simp_all

/--
A head built from a major type and argument is never a simple value. It rules out the decoder's
numeric branches as a source of simple values.

`Decode.Head.ofMajor major n` is one of the six constructors for major types 0 to 5, and the
inequality says it is not `.simple v` for any `v`.
-/
theorem ofMajor_ne_simple (major : Nat) (n : UInt64) (v : Value) :
    Decode.Head.ofMajor major n ≠ .simple v := by
  unfold Decode.Head.ofMajor
  repeat' split
  all_goals simp

/--
The only simple values the decoder's head reader produces are `false`, `true` and `null`. Every
other simple value and every float is refused, and this is the positive side of that refusal.

The hypothesis says `Decode.readHead` returned a simple head carrying `v`; the conclusion says `v`
is one of the three supported values.
-/
theorem readHead_simple_inv {input : ByteArray} {pos : Nat} {v : Value} {p}
    (h : Decode.readHead input pos = .ok (.simple v, p)) :
    v = .bool false ∨ v = .bool true ∨ v = .null := by
  unfold Decode.readHead at h
  dsimp only at h
  repeat' split at h
  all_goals simp only [Except.ok.injEq, Prod.mk.injEq, reduceCtorEq,
    Decode.Head.simple.injEq] at h
  all_goals first
    | (obtain ⟨rfl, _⟩ := h; simp)
    | (exact absurd h.1 (ofMajor_ne_simple _ _ _))

end Tests.Proofs
