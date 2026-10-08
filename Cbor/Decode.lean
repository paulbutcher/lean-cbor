/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cbor.Error
public import Cbor.Order
public import Cbor.Value

/-!
One decoder, enforcing canonical form as it reads. Each function returns, beside its result, a proof
that it consumed at least one byte and stayed within the input; the recursion terminates on the
bytes remaining, and that proof is what shows they shrink.

The array and map loops call themselves in tail position, so a declared count of millions costs no
stack. Nesting does, which is what `maxDepth` bounds.
-/

@[expose] public section

namespace Cbor.Decode

/-- A head, once every form this library refuses has been refused. -/
inductive Head where
  | uint (n : UInt64)
  | nint (n : UInt64)
  | bytes (n : UInt64)
  | text (n : UInt64)
  | array (n : UInt64)
  | map (n : UInt64)
  | simple (v : Value)

/-- Major types 0 to 5, the ones whose argument is a number or a length. -/
def Head.ofMajor (major : Nat) (n : UInt64) : Head :=
  if major == 0 then .uint n
  else if major == 1 then .nint n
  else if major == 2 then .bytes n
  else if major == 3 then .text n
  else if major == 4 then .array n
  else .map n

/-- A position strictly past `pos` and no further than the end of `input`. -/
abbrev After (input : ByteArray) (pos : Nat) := {p : Nat // pos < p ∧ p ≤ input.size}

def bigEndian (bytes : List UInt8) : Nat :=
  bytes.foldl (fun acc b => acc * 256 + b.toNat) 0

/-- The width of the argument that additional information 24 to 27 announces, and the least
argument that needs that width. Anything smaller had a shorter head. -/
def argumentForm (info : Nat) : Nat × Nat :=
  if info == 24 then (1, 24)
  else if info == 25 then (2, 0x100)
  else if info == 26 then (4, 0x10000)
  else (8, 0x100000000)

def readHead (input : ByteArray) (pos : Nat) : Except Error (Head × After input pos) :=
  if h : pos < input.size then
    let major := input[pos].toNat / 32
    let info := input[pos].toNat % 32
    let fail (reason : Reason) : Except Error (Head × After input pos) := .error ⟨reason, pos⟩
    let next : After input pos := ⟨pos + 1, by omega, by omega⟩
    if major == 7 then
      if info == 20 then .ok (.simple (.bool false), next)
      else if info == 21 then .ok (.simple (.bool true), next)
      else if info == 22 then .ok (.simple .null, next)
      else if 25 ≤ info ∧ info ≤ 27 then fail .float
      else if 28 ≤ info ∧ info ≤ 30 then fail .reservedInfo
      else if info == 31 then fail .unexpectedBreak
      else fail .unsupportedSimple
    else if 28 ≤ info ∧ info ≤ 30 then fail .reservedInfo
    else if info == 31 then
      if 2 ≤ major ∧ major ≤ 5 then fail .indefiniteLength else fail .reservedInfo
    else if major == 6 then fail .tag
    else
      if info < 24 then .ok (Head.ofMajor major (UInt64.ofNat info), next)
      else
        let (width, least) := argumentForm info
        if hw : pos + 1 + width ≤ input.size then
          let n := bigEndian (input.extract (pos + 1) (pos + 1 + width)).data.toList
          if n < least then fail .nonMinimalHead
          else .ok (Head.ofMajor major (UInt64.ofNat n), ⟨pos + 1 + width, by omega, hw⟩)
        else .error ⟨.truncated, input.size⟩
  else .error ⟨.truncated, pos⟩

/-- The `n` bytes at `p`, an item's content once its head, which began at `pos`, has been read. -/
def readSlice (input : ByteArray) (pos p : Nat) (hp : pos < p) (n : UInt64) :
    Except Error ({b : ByteArray // b.size < 2 ^ 64} × After input pos) :=
  if h : p + n.toNat ≤ input.size then
    .ok (⟨input.extract p (p + n.toNat), by rw [ByteArray.size_extract, Nat.min_eq_left h]; have := n.toNat_lt; omega⟩,
      ⟨p + n.toNat, by omega, h⟩)
  else .error ⟨.lengthExceedsInput, pos⟩

def readText (input : ByteArray) (pos p : Nat) (hp : pos < p) (n : UInt64) :
    Except Error ({s : String // s.utf8ByteSize < 2 ^ 64} × After input pos) :=
  match readSlice input pos p hp n with
  | .error e => .error e
  | .ok (⟨b, hb⟩, q) =>
    if hv : b.IsValidUTF8 then .ok (⟨String.fromUTF8 b hv, hb⟩, q)
    else .error ⟨.invalidUtf8, pos⟩

def readKey (input : ByteArray) (pos : Nat) : Except Error (Key × After input pos) :=
  match readHead input pos with
  | .error e => .error e
  | .ok (.uint n, p) => .ok (.uint n, p)
  | .ok (.nint n, p) => .ok (.nint n, p)
  | .ok (.text n, p) =>
    match readText input pos p.1 p.2.1 n with
    | .error e => .error e
    | .ok (⟨s, hs⟩, q) => .ok (.text s hs, q)
  | .ok _ => .error ⟨.unsupportedKey, pos⟩

/-- `.ok` exactly when the key encoded as `current` may follow the one encoded as `previous`. Keys
must strictly increase, so one comparison finds both an out-of-order key and a repeated one. -/
def checkOrder (previous : Option ByteArray) (current : ByteArray) (pos : Nat) :
    Except Error Unit :=
  match previous with
  | none => .ok ()
  | some previous =>
    match Order.compareEncoded previous current with
    | .lt => .ok ()
    | .eq => .error ⟨.duplicateKey, pos⟩
    | .gt => .error ⟨.unsortedKeys, pos⟩

mutual
/-- The item at `pos`, with arrays and maps allowed to nest `depth` more levels. -/
def item (input : ByteArray) (depth pos : Nat) : Except Error (Value × After input pos) :=
  match readHead input pos with
  | .error e => .error e
  | .ok (.simple v, p) => .ok (v, p)
  | .ok (.uint n, p) => .ok (.uint n, p)
  | .ok (.nint n, p) => .ok (.nint n, p)
  | .ok (.bytes n, p) =>
    match readSlice input pos p.1 p.2.1 n with
    | .error e => .error e
    | .ok (⟨b, hb⟩, q) => .ok (.bytes b hb, q)
  | .ok (.text n, p) =>
    match readText input pos p.1 p.2.1 n with
    | .error e => .error e
    | .ok (⟨s, hs⟩, q) => .ok (.text s hs, q)
  | .ok (.array n, ⟨p, hp⟩) =>
    match depth with
    | 0 => .error ⟨.tooDeep, pos⟩
    | d + 1 =>
      -- Every item is at least one byte, so a count beyond the bytes remaining cannot be met.
      if n.toNat ≤ input.size - p then
        match items input d p p n.toNat (Nat.le_refl p) hp.2 n.toNat [] (by simp) with
        | .error e => .error e
        | .ok (⟨xs, hxs⟩, ⟨q, hq⟩) =>
          .ok (.array xs (by have := n.toNat_lt; omega), ⟨q, by omega, hq.2⟩)
      else .error ⟨.lengthExceedsInput, pos⟩
  | .ok (.map n, ⟨p, hp⟩) =>
    match depth with
    | 0 => .error ⟨.tooDeep, pos⟩
    | d + 1 =>
      if n.toNat ≤ input.size - p then
        match entries input d p p n.toNat (Nat.le_refl p) hp.2 none n.toNat [] (by simp) with
        | .error e => .error e
        | .ok (⟨es, hes⟩, ⟨q, hq⟩) =>
          .ok (.map es (by have := n.toNat_lt; omega), ⟨q, by omega, hq.2⟩)
      else .error ⟨.lengthExceedsInput, pos⟩
termination_by (input.size - pos, 0)
decreasing_by all_goals (apply Prod.Lex.left; omega)

/-- The `remaining` items from `pos` onward of an array of `count` that began at `start`, with
`acc` holding those already read, most recent first. -/
def items (input : ByteArray) (depth start pos count : Nat) (hstart : start ≤ pos)
    (hpos : pos ≤ input.size) (remaining : Nat) (acc : List Value)
    (hacc : acc.length + remaining = count) :
    Except Error ({xs : List Value // xs.length = count} × {q : Nat // start ≤ q ∧ q ≤ input.size}) :=
  match remaining with
  | 0 => .ok (⟨acc.reverse, by simpa using hacc⟩, ⟨pos, hstart, hpos⟩)
  | r + 1 =>
    match item input depth pos with
    | .error e => .error e
    | .ok (v, ⟨p, hp⟩) =>
      items input depth start p count (by omega) hp.2 r (v :: acc) (by simp; omega)
termination_by (input.size - pos, 1)
decreasing_by
  · apply Prod.Lex.right; omega
  · apply Prod.Lex.left; omega

/-- As `items`, for the entries of a map, with `previous` the encoding of the last key read. -/
def entries (input : ByteArray) (depth start pos count : Nat) (hstart : start ≤ pos)
    (hpos : pos ≤ input.size) (previous : Option ByteArray) (remaining : Nat)
    (acc : List (Key × Value)) (hacc : acc.length + remaining = count) :
    Except Error
      ({es : List (Key × Value) // es.length = count} × {q : Nat // start ≤ q ∧ q ≤ input.size}) :=
  match remaining with
  | 0 => .ok (⟨acc.reverse, by simpa using hacc⟩, ⟨pos, hstart, hpos⟩)
  | r + 1 =>
    match readKey input pos with
    | .error e => .error e
    | .ok (k, ⟨kp, hkp⟩) =>
      let encoded := input.extract pos kp
      match checkOrder previous encoded pos with
      | .error e => .error e
      | .ok () =>
        match item input depth kp with
        | .error e => .error e
        | .ok (v, ⟨p, hp⟩) =>
          entries input depth start p count (by omega) hp.2 (some encoded) r ((k, v) :: acc)
            (by simp; omega)
termination_by (input.size - pos, 1)
decreasing_by
  · apply Prod.Lex.left; omega
  · apply Prod.Lex.left; omega
end

end Cbor.Decode

namespace Cbor

/-- The one item beginning at `offset`, and the offset just past it. Bytes after it are the
caller's: WebAuthn's `authenticatorData` follows its credential public key with extension data, and
this is how the end of the key is found. -/
def decodePrefix (input : ByteArray) (offset : Nat) : Except Error (Value × Nat) :=
  match Decode.item input maxDepth offset with
  | .error e => .error e
  | .ok (v, p) => .ok (v, p.1)

/-- The value `input` encodes, which must be the whole of it. -/
def decode (input : ByteArray) : Except Error Value :=
  match decodePrefix input 0 with
  | .error e => .error e
  | .ok (v, p) => if p = input.size then .ok v else .error ⟨.trailingBytes, p⟩

end Cbor
