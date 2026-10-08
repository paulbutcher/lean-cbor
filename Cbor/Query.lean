/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cbor.Value

/-!
Reading values without pattern matching at every call site. A key that is absent and a key whose
value has the wrong type are different errors, because they are different defects: a COSE key with
no `-2` label and one whose `-2` label is not a byte string have different causes.
-/

@[expose] public section

namespace Cbor

inductive Kind where
  | uint | nint | bytes | text | array | map | bool | null
deriving DecidableEq, Repr, Inhabited

def Kind.name : Kind → String
  | .uint => "uint"
  | .nint => "nint"
  | .bytes => "bytes"
  | .text => "text"
  | .array => "array"
  | .map => "map"
  | .bool => "bool"
  | .null => "null"

def Value.kind (v : Value) : Kind :=
  match v.item with
  | .uint _ => .uint
  | .nint _ => .nint
  | .bytes _ _ => .bytes
  | .text _ _ => .text
  | .array _ => .array
  | .map _ => .map
  | .bool _ => .bool
  | .null => .null

namespace Key

instance : ToString Key where
  toString
    | .uint n => toString n
    | .nint n => s!"-{n.toNat + 1}"
    | .text s _ => s.quote

end Key

inductive QueryError where
  /-- The value itself is not of the kind asked for. -/
  | wrongKind (expected actual : Kind)
  | missing (key : Key)
  /-- The key is present, but its value is not of the kind asked for. -/
  | wrongType (key : Key) (expected actual : Kind)
deriving Inhabited

/-- A short stable string for a log record or a span attribute. -/
def QueryError.name : QueryError → String
  | .wrongKind .. => "wrong_kind"
  | .missing _ => "missing"
  | .wrongType .. => "wrong_type"

instance : ToString QueryError where
  toString
    | .wrongKind e a => s!"expected {e.name}, found {a.name}"
    | .missing k => s!"key {k} is absent"
    | .wrongType k e a => s!"key {k} holds {a.name}, expected {e.name}"

namespace Value

def asInt (v : Value) : Except QueryError Int :=
  match v.item with
  | .uint n => .ok n.toNat
  | .nint n => .ok (-1 - n.toNat)
  | _ => .error (.wrongKind .uint v.kind)

def asBytes (v : Value) : Except QueryError ByteArray :=
  match v.view with
  | .bytes b => .ok b
  | _ => .error (.wrongKind .bytes v.kind)

def asText (v : Value) : Except QueryError String :=
  match v.view with
  | .text s => .ok s
  | _ => .error (.wrongKind .text v.kind)

def asBool (v : Value) : Except QueryError Bool :=
  match v.view with
  | .bool b => .ok b
  | _ => .error (.wrongKind .bool v.kind)

def asArray (v : Value) : Except QueryError (List Value) :=
  match v.view with
  | .array xs => .ok xs
  | _ => .error (.wrongKind .array v.kind)

def asMap (v : Value) : Except QueryError (List (Key × Value)) :=
  match v.view with
  | .map es => .ok es
  | _ => .error (.wrongKind .map v.kind)

/-- The value under `k`, taking the first entry when a hand-built map repeats a key. A decoded map
never does. -/
def find (v : Value) (k : Key) : Except QueryError Value := do
  match (← v.asMap).find? (·.1 == k) with
  | some (_, w) => .ok w
  | none => .error (.missing k)

/-- Looks up `k` and reads its value with `read`, reporting a value of the wrong kind against the
key it was found under. -/
def findAs {α : Type} (v : Value) (k : Key) (read : Value → Except QueryError α) :
    Except QueryError α := do
  let w ← v.find k
  match read w with
  | .error (.wrongKind expected actual) => .error (.wrongType k expected actual)
  | result => result

def intAt (v : Value) (k : Key) : Except QueryError Int := v.findAs k asInt
def bytesAt (v : Value) (k : Key) : Except QueryError ByteArray := v.findAs k asBytes
def textAt (v : Value) (k : Key) : Except QueryError String := v.findAs k asText
def boolAt (v : Value) (k : Key) : Except QueryError Bool := v.findAs k asBool
def arrayAt (v : Value) (k : Key) : Except QueryError (List Value) := v.findAs k asArray

/-- The map under `k`, as a `Value` so that lookups can continue into it. -/
def mapAt (v : Value) (k : Key) : Except QueryError Value :=
  v.findAs k fun w => w.asMap.map fun _ => w

end Value

end Cbor
