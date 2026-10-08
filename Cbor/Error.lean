/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

@[expose] public section

namespace Cbor

inductive Reason where
  /-- The input ends inside a head. -/
  | truncated
  /-- A declared length, or a declared count of items, is more than the bytes remaining could
  hold. -/
  | lengthExceedsInput
  /-- Additional information 28 to 30, or 31 on a major type with no indefinite form. -/
  | reservedInfo
  | indefiniteLength
  /-- The break code where no indefinite-length item is open, which here is everywhere. -/
  | unexpectedBreak
  | nonMinimalHead
  | tag
  | float
  /-- A simple value other than `false`, `true` and `null`. -/
  | unsupportedSimple
  /-- A map key that is neither an integer nor a text string. -/
  | unsupportedKey
  | unsortedKeys
  | duplicateKey
  | invalidUtf8
  | tooDeep
  | trailingBytes
deriving DecidableEq, Repr, Inhabited

/-- A short stable string for a log record or a span attribute. -/
def Reason.name : Reason → String
  | .truncated => "truncated"
  | .lengthExceedsInput => "length_exceeds_input"
  | .reservedInfo => "reserved_info"
  | .indefiniteLength => "indefinite_length"
  | .unexpectedBreak => "unexpected_break"
  | .nonMinimalHead => "non_minimal_head"
  | .tag => "tag"
  | .float => "float"
  | .unsupportedSimple => "unsupported_simple"
  | .unsupportedKey => "unsupported_key"
  | .unsortedKeys => "unsorted_keys"
  | .duplicateKey => "duplicate_key"
  | .invalidUtf8 => "invalid_utf8"
  | .tooDeep => "too_deep"
  | .trailingBytes => "trailing_bytes"

structure Error where
  reason : Reason
  /-- Where the offending item begins, or for `truncated` and `trailingBytes`, the first byte that
  is missing or left over. -/
  offset : Nat
deriving DecidableEq, Repr, Inhabited

def Error.name (e : Error) : String := e.reason.name

instance : ToString Error where
  toString e := s!"{e.reason.name} at offset {e.offset}"

end Cbor
