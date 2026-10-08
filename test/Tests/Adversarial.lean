/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cbor
public import Tests.Harness

/-!
RFC 8949 Appendix F.1, the items that are not well-formed, each with the reason this decoder gives
and where. Several are refused for a reason other than the one F.1 files them under, because this
decoder checks what it does not support before reading further: `d8` is a tag before it is a head
cut short, and `a2 00 00 00` repeats a key before it runs out of input.
-/

@[expose] public section

namespace Tests.Adversarial
open Cbor

def notWellFormed : List (String × Reason × Nat) := [
  -- End of input in a head.
  ("18", .truncated, 1), ("19", .truncated, 1), ("1a", .truncated, 1), ("1b", .truncated, 1),
  ("1901", .truncated, 2), ("1a0102", .truncated, 3), ("1b01020304050607", .truncated, 8),
  ("38", .truncated, 1), ("58", .truncated, 1), ("78", .truncated, 1), ("98", .truncated, 1),
  ("9a01ff00", .truncated, 4), ("b8", .truncated, 1), ("d8", .tag, 0),
  ("f8", .unsupportedSimple, 0), ("f900", .float, 0), ("fa0000", .float, 0),
  ("fb000000", .float, 0),
  -- Definite-length strings with short data.
  ("41", .lengthExceedsInput, 0), ("61", .lengthExceedsInput, 0),
  ("5affffffff00", .lengthExceedsInput, 0),
  ("5bffffffffffffffff010203", .lengthExceedsInput, 0),
  ("7affffffff00", .lengthExceedsInput, 0),
  ("7b7fffffffffffffff010203", .lengthExceedsInput, 0),
  -- Definite-length maps and arrays not closed with enough items.
  ("81", .lengthExceedsInput, 0), ("818181818181818181", .lengthExceedsInput, 8),
  ("8200", .lengthExceedsInput, 0), ("a1", .lengthExceedsInput, 0), ("a20102", .truncated, 3),
  ("a100", .truncated, 2), ("a2000000", .duplicateKey, 3),
  -- Tag number not followed by tag content.
  ("c0", .tag, 0),
  -- Indefinite-length strings, maps and arrays not closed by a break.
  ("5f4100", .indefiniteLength, 0), ("7f6100", .indefiniteLength, 0),
  ("9f", .indefiniteLength, 0), ("9f0102", .indefiniteLength, 0), ("bf", .indefiniteLength, 0),
  ("bf01020102", .indefiniteLength, 0), ("819f", .indefiniteLength, 1),
  ("9f8000", .indefiniteLength, 0), ("9f9f9f9f9fffffffff", .indefiniteLength, 0),
  ("9f819f819f9fffffff", .indefiniteLength, 0),
  -- Reserved additional information values.
  ("1c", .reservedInfo, 0), ("1d", .reservedInfo, 0), ("1e", .reservedInfo, 0),
  ("3c", .reservedInfo, 0), ("3d", .reservedInfo, 0), ("3e", .reservedInfo, 0),
  ("5c", .reservedInfo, 0), ("5d", .reservedInfo, 0), ("5e", .reservedInfo, 0),
  ("7c", .reservedInfo, 0), ("7d", .reservedInfo, 0), ("7e", .reservedInfo, 0),
  ("9c", .reservedInfo, 0), ("9d", .reservedInfo, 0), ("9e", .reservedInfo, 0),
  ("bc", .reservedInfo, 0), ("bd", .reservedInfo, 0), ("be", .reservedInfo, 0),
  ("dc", .reservedInfo, 0), ("dd", .reservedInfo, 0), ("de", .reservedInfo, 0),
  ("fc", .reservedInfo, 0), ("fd", .reservedInfo, 0), ("fe", .reservedInfo, 0),
  -- Reserved two-byte encodings of simple values.
  ("f800", .unsupportedSimple, 0), ("f801", .unsupportedSimple, 0),
  ("f818", .unsupportedSimple, 0), ("f81f", .unsupportedSimple, 0),
  -- Indefinite-length string chunks of the wrong type, or themselves indefinite.
  ("5f00ff", .indefiniteLength, 0), ("5f21ff", .indefiniteLength, 0),
  ("5f6100ff", .indefiniteLength, 0), ("5f80ff", .indefiniteLength, 0),
  ("5fa0ff", .indefiniteLength, 0), ("5fc000ff", .indefiniteLength, 0),
  ("5fe0ff", .indefiniteLength, 0), ("7f4100ff", .indefiniteLength, 0),
  ("5f5f4100ffff", .indefiniteLength, 0), ("7f7f6100ffff", .indefiniteLength, 0),
  -- A break outside an indefinite-length item.
  ("ff", .unexpectedBreak, 0), ("81ff", .unexpectedBreak, 1), ("8200ff", .unexpectedBreak, 2),
  ("a1ff", .unexpectedBreak, 1), ("a1ff00", .unexpectedBreak, 1),
  ("a100ff", .unexpectedBreak, 2), ("a20000ff", .unexpectedBreak, 3),
  ("9f81ff", .indefiniteLength, 0), ("9f829f819f9fffffffff", .indefiniteLength, 0),
  ("bf00ff", .indefiniteLength, 0), ("bf000000ff", .indefiniteLength, 0),
  -- Major types 0, 1 and 6 with additional information 31.
  ("1f", .reservedInfo, 0), ("3f", .reservedInfo, 0), ("df", .reservedInfo, 0)
]

def checks : List (String × Bool) :=
  notWellFormed.map fun (h, r, o) => (s!"Appendix F.1 refuses {h}", refuses (hex h) r o)

def nestedArrays (depth : Nat) : ByteArray :=
  ⟨Array.replicate depth 0x81⟩ ++ hex "00"

/-- Nesting exactly at the bound is decoded, re-encoded and compared on a dedicated thread, whose
stack may be smaller than the main thread's, so that the margin `maxDepth` relies on is tested
rather than assumed. -/
def atDepthBound : IO Bool := do
  let task ← IO.asTask (prio := .dedicated) do
    let input := nestedArrays maxDepth
    match decode input with
    | .ok v => return bytesEq v.encode input && v.withinDepth
    | .error _ => return false
  match task.get with
  | .ok passed => return passed
  | .error _ => return false

def ioChecks : IO (List (String × Bool)) := do
  return [("nesting at the depth bound round-trips on another thread", ← atDepthBound)]

end Tests.Adversarial
