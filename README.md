# cbor

Deterministic CBOR for Lean 4: one encoding per value, and a decoder that accepts nothing else. It is written for consumers to whom two encodings of one value are a defect, such as COSE keys, WebAuthn attestation objects and CTAP2 messages.

Nothing in it is `partial`, nothing in it can panic, and it depends on nothing beyond the Lean toolchain.

## Installing

In `lakefile.toml`:

```toml
[[require]]
name = "cbor"
git = "https://github.com/paulbutcher/lean-cbor.git"
```

## Reading and writing

```lean
import Cbor
open Cbor

-- Entries may be given in any order: `encode` sorts them.
#eval (Value.map [(.ofInt 3, .int (-7)), (.ofInt 1, .int 2)]).encode   -- [162, 1, 2, 3, 38]

#eval decode ⟨#[0xa2, 0x02, 0x00, 0x01, 0x00]⟩
-- Except.error { reason := Cbor.Reason.unsortedKeys, offset := 3 }

def algorithm (bytes : ByteArray) : Except String Int := do
  let key ← (decode bytes).mapError toString
  (key.intAt (.ofInt 3)).mapError toString
```

| | |
|---|---|
| `decode (input : ByteArray) : Except Error Value` | the whole input must be one item |
| `decodePrefix (input : ByteArray) (offset : Nat) : Except Error (Value × Nat)` | one item, and the offset just past it |
| `Value.encode (v : Value) : ByteArray` | always canonical |

`decodePrefix` is how a credential public key is found inside WebAuthn's `authenticatorData`, where it is followed by optional extension data.

## Values

`Value` holds unsigned and negative integers, byte strings, text, arrays, maps, `false`, `true` and `null`. Map keys are integers or text strings, and every length is below `2^64`, so every value has an encoding. Literals need no proofs: `Value.text "a"`, `Value.int (-7)`, `Key.ofInt (-2)`. Data whose size is not known at compile time goes through `Value.bytes?`, `Value.text?`, `Value.array?` and `Value.map?`.

`Value.view` takes one layer apart for pattern matching. `Value.distinctKeys` reports whether any map repeats a key, which `encode` cannot refuse but `decode` will, and `Value.withinDepth` whether nesting is within the decoder's bound.

## Queries

`intAt`, `bytesAt`, `textAt`, `boolAt`, `arrayAt` and `mapAt` read a map by key, and `asInt`, `asBytes` and the rest read a value directly. A key that is absent and a key holding the wrong kind of value are different errors, `missing` and `wrongType`, since they have different causes. When a hand-built map repeats a key, the first entry is the one found.

## What is refused

Each refusal names its reason and the byte offset where it was found; `Error.name` gives a stable string for a log or a span attribute.

- Tags, floats, simple values other than `false`, `true` and `null`, indefinite lengths, and map keys that are neither integers nor text.
- Anything not in canonical form: a head longer than its argument needs, map keys out of order or repeated, and bytes after the item.
- Invalid UTF-8, reserved additional information, and input that ends early or declares more than it holds.
- Nesting deeper than 1024. The bound is fixed: decoding, encoding and comparison recurse on the stack, and a fixed bound is what keeps hostile input from exhausting it. A value built by hand deeper than that may overflow.

The canonical form is CTAP2's, which WebAuthn specifies. Map keys sort by major type, then encoded length, then bytes. For integer and text keys this agrees with RFC 8949 §4.2.1's deterministic encoding.

## What is verified

Proved as theorems, for all inputs, in `test`:

- `decode` of `encode v` gives back `v` with its maps sorted, for every `v` with distinct keys and nesting within the bound, which every decoded value has.
- If `decode` accepts some bytes, `encode` of the result is exactly those bytes. Two different byte strings never decode to the same value.
- Every decoded value is already sorted, and sorting is idempotent, so a decoded value round-trips to itself exactly.
- `decodePrefix` finds an encoded value among any surrounding bytes and reports exactly where it ends; `decode` refuses anything after a complete item.
- A lookup reports a key absent exactly when no entry has it, and otherwise finds the first.

Checked against published vectors and captures:

- Every example in RFC 8949 Appendix A, in both directions, and the refusal of every one outside the supported subset, with its reason.
- Every malformed example in RFC 8949 Appendix F.1, with its reason and offset.
- The attestation objects of WebAuthn Level 3's test vectors, and attestation objects captured from YubiKey, Android, Apple and TPM authenticators by py_webauthn, each decoded down to its credential public key.
- Nesting at the depth bound, decoded and re-encoded on a thread other than the main one.

## Building

```
lake build
lake test
```

## Licence

Apache 2.0. The test fixtures taken from the WebAuthn specification and from py_webauthn carry their own notices.
