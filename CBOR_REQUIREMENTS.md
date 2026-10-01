# lean-cbor requirements

Requirements for a reusable Lean 4 library providing deterministic CBOR encoding and decoding. Written for an implementer working in this package, `cbor`, whose library is `Cbor`. The published name `lean-cbor` is a placeholder; confirm it before publishing.

Requirement keywords: **MUST**, **SHOULD**, **MAY**. Requirements are numbered so that implementation and review can refer to them.

The reference texts are RFC 8949 for CBOR itself, and the Client to Authenticator Protocol (CTAP2) for the canonical encoding form. CBOR-6.2 says where they differ and which one wins.

---

## 1. Purpose and scope

`lean-cbor` turns CBOR bytes into values and values into CBOR bytes, in a form where the bytes are a function of the value. Its consumers are those for which two encodings of one value is a defect rather than a curiosity: COSE keys, WebAuthn attestation objects, CTAP2 messages, and signature inputs the caller encodes itself. Tagged COSE messages such as `COSE_Sign1` are out of scope until tags are; see 13.3. Interpreting what it decodes, such as turning a `COSE_Key` into a public key, belongs to the consumer, alongside the cryptography in `leancrypto` and `jose-libcrypto`.

It provides:

- A value type covering exactly the subset this library supports, so that every value of the type is encodable.
- A total decoder that requires canonical form and reports how many bytes it consumed.
- An encoder that emits one encoding per value, always canonical.
- Queries for reading maps and arrays without writing pattern matches at every call site.
- Theorems that the round trip holds and that a canonical encoding is unique.

### 1.1 Non-goals for the first version

- Tags (major type 6), including bignums and decimal fractions. See 13.3.
- Indefinite-length items. CTAP2 forbids them and they are a source of encoding ambiguity.
- Floating point, and every simple value other than `false`, `true` and `null`. RFC 8949's deterministic rule for floats is the shortest form that round-trips, which is fiddly, and no target consumer needs one.
- Map keys other than integers and text strings. See CBOR-4.3 and 13.2.
- Streaming decoding from a chunked source, any textual rendering beyond `Repr`, and a `ToCbor` / `FromCbor` typeclass with a deriving layer. See 13.1 and 13.4.

- **CBOR-1.1** A well-formed CBOR item outside the supported subset MUST be rejected with a reason naming why. It MUST NOT be skipped, coerced, or partially read. This is the whole safety posture of the library: a consumer verifying a signature over bytes it did not fully understand is the failure this exists to prevent.

---

## 2. Target environment

- **CBOR-2.1** Toolchain `leanprover/lean4:v4.33.1`, matching the sibling libraries a consumer is likely to require alongside this one.
- **CBOR-2.2** The library MUST have no dependencies at all, beyond what the toolchain ships. Pure Lean, no native library, no `pkg-config`. A consumer taking this package acquires nothing else, which is most of the reason for it to be a package rather than a module inside its first consumer.
- **CBOR-2.3** The lakefile MUST set `autoImplicit` and `relaxedAutoImplicit` false and `warningAsError` true.
- **CBOR-2.4** Tests follow the layout in `CLAUDE.md`. The root lakefile MUST therefore be `lakefile.lean`, since a TOML lakefile cannot carry the `@[test_driver]` script.

---

## 3. Architecture

- **CBOR-3.1** The module layout SHOULD mirror `lean-json`, which solves the same shape of problem: a value type, a decoder, an encoder, queries, and separate modules carrying the theorems. An implementer unfamiliar with that layout should read it from a fresh checkout of [`lean-json`](https://github.com/paulbutcher/lean-json), not from a copy under `.lake`.
- **CBOR-3.2** Nothing may be `partial`, and nothing may call a function that panics on bad input. Decoding and encoding MUST be pure: neither takes a monad, and neither performs an effect. The decoder recurses, so it needs a well-founded measure; the count of bytes remaining is the natural one.

---

## 4. The data model

- **CBOR-4.1** The value type MUST represent unsigned and negative integers as two separate constructors over `UInt64`, the negative one standing for `-1 - n`, rather than as a single `Int`. CBOR integers span `-2^64` to `2^64 - 1`, which no fixed-width signed type holds, and `Int` would admit values the encoder cannot emit. A convenience `toInt` returning `Option Int` SHOULD be provided, since callers reason in integers.
- **CBOR-4.2** Byte strings, text strings, arrays and maps MUST carry a proof that their length, in bytes for strings and in items or entries otherwise, is below `2^64`. A CBOR head cannot declare a larger length, and without the bound every theorem would carry a size hypothesis. Checked constructors returning `Option` SHOULD be provided so that callers holding data of unknown size need not discharge the proof by hand.
- **CBOR-4.3** Map entries MUST be held as an ordered sequence of key-value pairs, not as a lookup structure, so that duplicate keys are detectable rather than silently collapsed. Keys MUST be integers or text strings, held in their own type. These are all COSE and CTAP2 use, and for them value equality coincides with equality of encodings and CTAP2's ordering coincides with RFC 8949's (CBOR-6.2), neither of which holds once keys can be arrays or maps.
- **CBOR-4.4** Text strings are UTF-8. The decoder MUST validate and reject invalid UTF-8 rather than substituting replacement characters. Substitution changes the value, which breaks the round trip silently and in the one direction nobody checks.
- **CBOR-4.5** Equality MUST be decidable, and `BEq` MUST be lawful. `Repr` SHOULD elide a byte string beyond a modest length, so that a decoded value reaching a log does not dump an arbitrary payload into it.

---

## 5. Decoding

- **CBOR-5.1** `decode` takes a `ByteArray` and returns either one value or an error. The whole input MUST be one item: bytes left over are an error and MUST NOT be ignored. A decoder that tolerates trailing bytes lets two different inputs be accepted as the same value, which is a parsing differential and the classic way a signature ends up covering something other than what was checked.
- **CBOR-5.2** `decodePrefix` MUST also be provided, taking an offset, decoding one item, and returning the value together with the offset just past it. WebAuthn's `authenticatorData` carries the credential public key as a CBOR item followed by optional extension data, so a consumer cannot find the end of the key any other way.
- **CBOR-5.3** The decoder MUST reject, each with its own reason: indefinite-length items; tags; unsupported simple values and floats; map keys other than integers and text strings; non-minimal heads; map keys out of canonical order; duplicate map keys; invalid UTF-8; nesting beyond the depth bound; trailing bytes; reserved additional-information values; and input that ends early. A non-minimal head is well-formed under RFC 8949 but is a second encoding of a value that already has one. Duplicate keys let two readers disagree about one document, since which entry a reader takes is unspecified.
- **CBOR-5.4** The error type MUST distinguish every reason in CBOR-5.3 and carry the byte offset at which it was found. It MUST provide a `name` giving each reason a short stable string for a log record or a span attribute. "Malformed" in a log ends no investigation.

---

## 6. Canonical form

- **CBOR-6.1** The canonical form is CTAP2's. Integers use the shortest head that holds them. Lengths are definite. Map keys are sorted: a lower major type sorts earlier; among keys of the same major type, the shorter encoding sorts earlier; among keys encoding to the same length, the lower byte-wise lexical value sorts earlier.
- **CBOR-6.2** For integer and text keys, CBOR-6.1 coincides with RFC 8949 §4.2.1's byte-wise ordering of encoded keys: the major type occupies the top bits of the first byte, and within one major type a minimal head grows with the value or length. The rules diverge only for compound keys: `[1000]` (`81 19 03 e8`) precedes `[1,2]` (`82 01 02`) byte-wise but follows it under CTAP2. RFC 8949 §4.2.3's length-first rule differs again, lacking the major type step: it puts `""` (`60`) before `24` (`18 18`). WebAuthn specifies CTAP2's form, so any extension of the key type MUST keep CBOR-6.1 rather than adopt either RFC rule.
- **CBOR-6.3** There is one decode, and it enforces CBOR-6.1 inline as it reads. A map whose keys are out of order is refused where the violation is found, rather than recorded and handed back for the caller to judge. No mode, no flag, and no second entry point that tolerates non-canonical input.
- **CBOR-6.4** Enforcing inline means the check reaches every part of a document, including the parts a caller never reads, since CBOR-1.1 forbids passing over bytes without understanding them. A consumer reading a WebAuthn attestation object therefore refuses it for a quirk anywhere inside, `attStmt` included. That buys consistency rather than signature safety: WebAuthn signatures cover the raw `authenticatorData` bytes and the client data hash, not a decoded value. The cost is accepted; see 13.5.
- **CBOR-6.5** Ordering and duplicate detection are one comparison and MUST be implemented as one. Canonical keys strictly increase, so comparing each key against its predecessor answers both: greater is well formed, equal is a duplicate, and lower is out of order. The decoder SHOULD compare keys as slices of its input rather than re-encoding them.

---

## 7. Encoding

- **CBOR-7.1** `encode` MUST be total: every value of the type has an encoding, with no error case and no `Option`. CBOR-4.1 and CBOR-4.2 are what make this true.
- **CBOR-7.2** `encode` MUST always emit canonical form, sorting map entries itself. A caller that built a map in a convenient order still gets canonical bytes out, which is what makes the encoder safe to use for a signature input.
- **CBOR-7.3** Because CBOR-7.2 sorts, `encode` is not injective on values that differ only in the order of their map entries. The theorems in §10 MUST account for this rather than being weakened to hide it.
- **CBOR-7.4** `encode` on a value carrying duplicate map keys produces bytes the decoder will reject. Predicates reporting whether a value has distinct keys throughout, and whether it is within the depth bound of CBOR-9.2, MUST be provided, so these are conditions a caller can check rather than traps. The depth predicate MUST stop descending at the bound, or it would overflow on the very values it exists to catch.
- **CBOR-7.5** Output SHOULD be built without repeated copying of the whole buffer. A nested document should not cost quadratic time in its own size.

---

## 8. Queries

- **CBOR-8.1** Reading a map by integer key and by text key MUST be supported directly, without the caller pattern matching over entries. COSE labels are small integers and this is the library's commonest use.
- **CBOR-8.2** A key that is absent and a key whose value is of the wrong type MUST be distinguishable. "This COSE key has no `-1` label" and "its `-1` label is not a byte string" are different defects with different causes, and an accessor that returns `none` for both leaves the caller unable to say which it met.
- **CBOR-8.3** On a hand-built value with duplicate keys, a lookup returns the first matching entry. A decoded value never has duplicates, by CBOR-5.3.

---

## 9. Resource bounds

- **CBOR-9.1** The decoder MUST NOT allocate on a declared length before confirming the input actually holds that many bytes. A nine-byte head can declare a byte string of `2^64 - 1`, and a decoder that trusts it is a one-packet denial of service. A declared array or map count cannot be confirmed up front, so it MUST NOT exceed the bytes remaining, every item being at least one byte, and nothing may be preallocated from it.
- **CBOR-9.2** The decoder MUST refuse nesting deeper than a fixed bound of 1024, which callers cannot raise. Each level costs one byte of input, and every traversal recurses on the stack, so the bound is what keeps hostile input from exhausting it; a raisable bound would trade that guarantee for depth no target consumer needs. A value built by hand never meets the bound, so one deeper than it MAY overflow the stack in any traversal, and the documentation MUST say so. This is where the library departs from `lean-json`, whose traversals run on the heap.
- **CBOR-9.3** The depth bound MUST NOT make the theorems of §10 vacuous, and each theorem's doc comment MUST say why it does not. A round-trip theorem that holds only for values shallower than the bound is the theorem that was wanted, but it says so only if it says what the bound admits.

---

## 10. Theorems

These MUST be theorems rather than tests. They concern pure total functions, and a counterexample in any of them is a correctness defect in something signing or verifying bytes.

- **CBOR-10.1** Round trip: for every value with distinct keys throughout and depth within the bound, decoding its encoding yields its normalisation, the value with every map's entries sorted by CBOR-6.1. Stated against the normalisation rather than the value itself, because of CBOR-7.3.
- **CBOR-10.2** Every value the decoder produces is normalised, and normalising a normalised value returns it unchanged. Together with CBOR-10.1 this says a decoded value round-trips to itself exactly.
- **CBOR-10.3** Uniqueness: if the decode accepts some bytes and yields a value, then encoding that value returns exactly those bytes. This is the theorem that earns the library its purpose, because it makes canonicity a property of the decoder rather than a check every caller has to remember.
- **CBOR-10.4** Where a theorem carries a hypothesis that map keys are distinct, its doc comment MUST say why the hypothesis is not doing the work: every value the decoder produces satisfies it, by CBOR-5.3.

---

## 11. Testing

- **CBOR-11.1** RFC 8949 Appendix A's example table MUST be transcribed from the RFC, committed as fixtures, and run in both directions. It is the nearest thing this format has to a conformance suite. The machine-readable copy in `cbor/test-vectors` is RFC 7049's table and carries no licence, so it is a cross-check rather than the source.
- **CBOR-11.2** The Appendix A entries that fall outside the supported subset are tests too, of the rejection path: each MUST be refused, with the reason asserted and not merely the refusal.
- **CBOR-11.3** COSE public keys for ES256, RS256 and EdDSA, and WebAuthn attestation objects, MUST be committed as fixtures and decoded, each recording its source and licence. WebAuthn Level 3 §16 (W3C Software and Document License) supplies attestation objects in hex for packed, TPM, Android Key, Apple, FIDO U2F and none attestation, with credential keys for ES256, ES384, ES512, RS256, Ed25519 and Ed448, each reached through `decodePrefix` as CBOR-5.2 describes. The tests of [`py_webauthn`](https://github.com/duo-labs/py_webauthn) (BSD-3-Clause) supply captures from real authenticators, which are what say the library accepts what devices emit rather than what a specification's generator does.
- **CBOR-11.4** Adversarial cases MUST be covered at minimum: a declared length beyond the end of the input; a declared count beyond the bytes remaining; nesting past the depth bound; nesting exactly at the bound, which MUST decode, re-encode and compare equal on a thread other than the main one, whose stack may be smaller, so that the margin CBOR-9.2 relies on is tested rather than assumed; duplicate keys; a non-minimal head; an indefinite-length item; a map key that is neither an integer nor a text string; invalid UTF-8 in a text string; trailing bytes after a complete item; empty input; and a map whose keys are out of canonical order, both at the top level and inside a nested value. The nested case matters because the cost accepted in CBOR-6.4 is only bought if the check really does reach everywhere. RFC 8949 Appendix F.1's items that are not well-formed MUST be among them.
- **CBOR-11.5** The suite MUST make no network request when it runs and need no native dependency, so that `lake test` runs anywhere the toolchain does. Fixtures are written in hex and decoded with `Leancrypto.Codec.Hex`; the test subproject, and only it, requires [`leancrypto`](https://github.com/paulbutcher/leancrypto) at a tagged release.

---

## 12. Code standards

The code standards, including those for documenting theorems and for verifying a change, are in `CLAUDE.md`.

---

## 13. Open decisions

Unresolved unless the entry says otherwise. Each needs an answer before the affected part is built; a recommendation is offered but the decision is not the implementer's to make. Ask, do not assume.

- **13.1 A typeclass and deriving layer.** `lean-json` carries `ToJson` / `FromJson` and a deriving macro in separate targets. The first consumer here reads COSE maps by querying them and needs none of it. Recommendation: out for now, added as its own target when something wants it, so the core stays dependency-free and small.
- **13.2 Compound map keys.** Byte strings, arrays, maps and simple values as keys. Recommendation: not until something needs them. Adding them means keeping CTAP2's ordering where it diverges from RFC 8949's (CBOR-6.2), judging duplicates on encodings since two maps differing only in entry order are unequal values with one encoding, and normalising inside keys as well as values.
- **13.3 Floats, the remaining simple values, and tags.** Needed by anything using this as a general CBOR library rather than as a COSE one. Recommendation: defer, and make sure CBOR-1.1 means the omission is visible rather than silent. Bignums, tags 2 and 3, would be the first tags to arrive, and they interact with CBOR-4.1's integer representation.
- **13.4 Streaming.** A decoder over a chunked source, for inputs too large to hold. No target consumer has one; a WebAuthn attestation object is a few hundred bytes.
- **13.5 Tolerating non-canonical map ordering.** Answered: not built, which is what CBOR-6.3 records. The library's value is that bytes are a function of the value, and CBOR-6.4 shows the cost of strictness is availability rather than security. Strictness is also self-diagnosing: a device that violates canonical form produces a named refusal in a log, and that refusal is the evidence which would justify reopening this. Reopening means a second function whose name says what it surrenders, never a change to what `decode` does. It also means touching the decoder and re-checking the proofs that unfold it, which is the price of enforcing inline rather than reporting, and is accepted.

---

## 14. Suggested delivery order

Each step ends somewhere the build and the tests pass.

1. The value type with its length bounds, the encoder, and the ordering rule of CBOR-6.1.
2. The decoder with its error type, enforcing CBOR-6.1 inline and requiring the whole input.
3. The Appendix A vectors in both directions, including the refusals of CBOR-11.2.
4. The round trip and normalisation theorems, CBOR-10.1 and CBOR-10.2.
5. The uniqueness theorem, CBOR-10.3.
6. `decodePrefix`, the resource bounds of §9, and the adversarial suite.
7. Queries, and the COSE and attestation fixtures.

The theorems come before the bounds deliberately. A depth bound added to a decoder whose round trip is already proved is a hypothesis to discharge; one present from the start tends to be proved around rather than through.
