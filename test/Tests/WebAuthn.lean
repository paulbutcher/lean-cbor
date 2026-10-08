/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cbor
public import Tests.Harness
public import Tests.Fixtures.W3c
public import Tests.Fixtures.PyWebauthn
public import Leancrypto.Codec.Base64Url
public import Leancrypto.Codec.Base64

/-!
Attestation objects decoded as a relying party would decode them: the outer map, then the
credential public key found inside `authData` with `decodePrefix`, then whatever follows it.
-/

@[expose] public section

namespace Tests.WebAuthn
open Cbor

def describe {α : Type} {ε : Type} [ToString ε] : Except ε α → Except String α :=
  Except.mapError toString

def byteAt (b : ByteArray) (i : Nat) : Except String Nat :=
  match b[i]? with
  | some x => .ok x.toNat
  | none => .error s!"authData ends before byte {i}"

/-- The credential public key in an attestation object. `authData` is a 32-byte RP ID hash, a flags
byte, a 4-byte counter, a 16-byte AAGUID, a 2-byte credential ID length and the credential ID,
then the key, then extensions if the flags announce them. -/
def credentialKey (attestationObject : ByteArray) : Except String Value := do
  let v ← describe (decode attestationObject)
  let _ ← describe (v.textAt (.ofText "fmt"))
  let _ ← describe (v.mapAt (.ofText "attStmt"))
  let authData ← describe (v.bytesAt (.ofText "authData"))
  let flags ← byteAt authData 32
  if flags &&& 0x40 == 0 then throw "no attested credential data"
  let idLength := (← byteAt authData 53) * 256 + (← byteAt authData 54)
  let (key, next) ← describe (decodePrefix authData (55 + idLength))
  if flags &&& 0x80 != 0 then
    let extensions ← describe (decode (authData.extract next authData.size))
    let _ ← describe extensions.asMap
  else if next != authData.size then
    throw "bytes follow the credential public key with no extensions flagged"
  return key

/-- The key type, algorithm and, for curve keys, curve: COSE labels 1, 3 and -1. -/
def keySummary (key : Value) : Except String (Int × Int × Option Int) := do
  let kty ← describe (key.intAt (.ofInt 1))
  let alg ← describe (key.intAt (.ofInt 3))
  let crv := (key.intAt (.ofInt (-1))).toOption
  return (kty, alg, crv)

/-- What each section's title says its credential is, as COSE key type, algorithm and curve. Ed448
is -53, its fully specified identifier: the specification reserves -8, EdDSA, for Ed25519. -/
def w3cExpected : List (String × Int × Int × Option Int) := [
  ("16.2", 2, -7, some 1), ("16.3", 2, -7, some 1), ("16.6", 2, -7, some 1),
  ("16.7", 2, -7, some 1), ("16.8", 2, -35, some 2), ("16.9", 2, -36, some 3),
  ("16.10", 3, -257, none), ("16.11", 1, -8, some 6), ("16.12", 1, -53, some 7),
  ("16.13", 2, -7, some 1), ("16.14", 2, -7, some 1), ("16.15", 2, -7, some 1),
  ("16.16", 2, -7, some 1)
]

def w3cChecks : List (String × Bool) :=
  Fixtures.W3c.attestationObjects.map fun (name, h) =>
    let number := (name.splitOn " ").headD ""
    let expected := (w3cExpected.find? (·.1 == number)).map (·.2)
    let actual := (credentialKey (hex h) >>= keySummary).toOption
    (s!"WebAuthn {name}", expected.isSome && actual == expected)

def bytesOf (c : Fixtures.PyWebauthn.Capture) : Option ByteArray :=
  match c.encoding with
  | .base64url => Leancrypto.Codec.Base64Url.decodeString c.text
  | .base64 => Leancrypto.Codec.Base64.decodeString c.text

def captureChecks : List (String × Bool) :=
  Fixtures.PyWebauthn.attestationObjects.map fun c =>
    let decoded := match bytesOf c with
      | some b => (credentialKey b >>= keySummary).toBool
      | none => false
    (s!"py_webauthn {c.label}", decoded)

def b64url (s : String) : ByteArray := (Leancrypto.Codec.Base64Url.decodeString s).getD .empty

def ec2 : Option Value := (decode (b64url Fixtures.PyWebauthn.ec2Key)).toOption
def rsa : Option Value := (decode (b64url Fixtures.PyWebauthn.rsaKey)).toOption

def sizeAt (key : Option Value) (label : Int)
    (h : -2 ^ 64 ≤ label ∧ label < 2 ^ 64 := by decide) : Option Nat :=
  key.bind fun k => (k.bytesAt (.ofInt label h)).toOption.map (·.size)

/-- The expectations are py_webauthn's own, from the tests these keys were taken from. -/
def keyChecks : List (String × Bool) := [
  ("EC2 key type, algorithm and curve",
    ec2.bind (keySummary · |>.toOption) == some (2, -7, some 1)),
  ("EC2 coordinates are 32 bytes each", sizeAt ec2 (-2) == some 32 && sizeAt ec2 (-3) == some 32),
  ("RSA key type and algorithm", rsa.bind (keySummary · |>.toOption) == some (3, -257, none)),
  ("RSA modulus is 256 bytes", sizeAt rsa (-1) == some 256),
  ("RSA exponent is 65537",
    (rsa.bind fun k => (k.bytesAt (.ofInt (-2))).toOption.map (·.toList)) == some [1, 0, 1]),
  ("an absent label is reported as absent",
    match ec2.map (·.intAt (.ofInt (-4))) with
    | some (Except.error (QueryError.missing _)) => true
    | _ => false),
  ("a label holding the wrong kind is reported as such",
    match ec2.map (·.intAt (.ofInt (-2))) with
    | some (Except.error (QueryError.wrongType _ .uint .bytes)) => true
    | _ => false)
]

def checks : List (String × Bool) := w3cChecks ++ captureChecks ++ keyChecks

end Tests.WebAuthn
