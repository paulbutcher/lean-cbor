# lean-cbor requirements

Requirements for a reusable Lean 4 library providing deterministic CBOR encoding and decoding. Written to be handed to an implementer working in a freshly created package (`lake new lean-cbor lib`). The name `lean-cbor` is a placeholder; confirm it before publishing.

Requirement keywords: **MUST**, **SHOULD**, **MAY**. Requirements are numbered so that implementation and review can refer to them.

The reference texts are RFC 8949 for CBOR itself, and the Client to Authenticator Protocol (CTAP2) for the canonical encoding form. Where they differ, CBOR-6 says which one wins and why.

---

## 1. Purpose and scope

`lean-cbor` turns CBOR bytes into values and values into CBOR bytes, in a form where the bytes are a function of the value. Its consumers are those for which two encodings of one value is a defect rather than a curiosity: COSE keys, WebAuthn attestation objects, CTAP2 messages, and signature inputs generally.

It provides:

- A value type covering exactly the subset this library supports, so that every value of the type is encodable.
- A total decoder that requires canonical form and reports how many bytes it consumed.
- An encoder that emits one encoding per value, always canonical.
- Queries for reading maps and arrays without writing pattern matches at every call site.
- Theorems that the round trip holds and that a canonical encoding is unique.

### 1.1 Non-goals for the first version

- Tags (major type 6), including bignums and decimal fractions. See §13.
- Indefinite-length items. CTAP2 forbids them and they are a source of encoding ambiguity.
- Floating point, and every simple value other than `false`, `true` and `null`. RFC 8949's deterministic rule for floats is the shortest form that round-trips, which is fiddly, and no target consumer needs one.
- Streaming or incremental decoding from a chunked source.
- Diagnostic notation, CBOR-to-JSON, or any textual rendering beyond `Repr`.
- A `ToCbor` / `FromCbor` typeclass and a deriving layer. See §13.

- **CBOR-1.1** A well-formed CBOR item outside the supported subset MUST be rejected with a reason naming why. It MUST NOT be skipped, coerced, or partially read. This is the whole safety posture of the library: a consumer verifying a signature over bytes it did not fully understand is the failure this exists to prevent.

---

## 2. Target environment

- **CBOR-2.1** Toolchain `leanprover/lean4:v4.33.1`.
- **CBOR-2.2** The library MUST have no dependencies at all, beyond what the toolchain ships. Pure Lean, no native library, no `pkg-config`. A consumer taking this package acquires nothing else, which is most of the reason for it to be a package rather than a module inside its first consumer.
- **CBOR-2.3** The lakefile MUST set `autoImplicit` and `relaxedAutoImplicit` false and `warningAsError` true.
- **CBOR-2.4** Tests MUST live in a `test/` subproject with its own lakefile requiring the root package by path, so that nothing needed only for development appears in the dependency graph a downstream consumer resolves. The root lakefile carries the driver:

      @[test_driver]
      script tests do
        let child ← IO.Process.spawn
          { cmd := "lake", args := #["test"], cwd := __dir__ / "test" }
        child.wait

---

## 3. Architecture

- **CBOR-3.1** The module layout SHOULD mirror `lean-json`, which solves the same shape of problem: a value type, a decoder, an encoder, queries, and separate modules carrying the theorems. An implementer unfamiliar with that layout should read it from a fresh checkout of `lean-json`, not from a copy under `.lake`.
- **CBOR-3.2** Nothing may be `partial`, and nothing may call a function that panics on bad input. The decoder recurses, so it needs a well-founded measure; the count of bytes remaining is the natural one.
- **CBOR-3.3** Decoding and encoding MUST be pure. Neither takes a monad, and neither performs an effect.

---

## 4. The data model

- **CBOR-4.1** The value type MUST represent unsigned and negative integers as two separate constructors over `UInt64`, the negative one standing for `-1 - n`, rather than as a single `Int`. CBOR integers span `-2^64` to `2^64 - 1`, which no fixed-width signed type holds. Using `Int` would admit values the encoder cannot emit, and every theorem below would then carry a range hypothesis. Two constructors make the type exactly the encodable values, so `encode` is total.
- **CBOR-4.2** A convenience `toInt` returning `Option Int` SHOULD be provided, since callers reason in integers and COSE labels are small.
- **CBOR-4.3** Map entries MUST be held as an ordered sequence of key-value pairs, not as a lookup structure. The order is part of what canonicity is about, and duplicate keys have to be detectable rather than silently collapsed.
- **CBOR-4.4** Keys MAY be any value of the type. COSE uses integers and text strings, but restricting the type to those buys nothing and would make the ordering rule of CBOR-6.1 unstatable.
- **CBOR-4.5** Text strings are UTF-8. The decoder MUST validate and reject invalid UTF-8 rather than substituting replacement characters. Substitution changes the value, which breaks the round trip silently and in the one direction nobody checks.
- **CBOR-4.6** Equality MUST be decidable, and `BEq` MUST agree with it.
- **CBOR-4.7** `Repr` SHOULD elide a byte string beyond a modest length rather than printing all of it. A decoded value reaching a log should not dump an arbitrary payload into it.

---

## 5. Decoding

- **CBOR-5.1** `decode` takes a `ByteArray` and returns either one value or an error. The whole input MUST be one item: bytes left over are an error and MUST NOT be ignored. A decoder that tolerates trailing bytes lets two different inputs be accepted as the same value, which is a parsing differential and the classic way a signature ends up covering something other than what was checked.
- **CBOR-5.2** `decodePrefix` MUST also be provided, taking an offset, decoding one item, and returning the value together with the offset just past it. This is not a convenience. WebAuthn's `authenticatorData` carries the credential public key as a CBOR item followed by optional extension data, so a consumer cannot find the end of the key any other way.
- **CBOR-5.3** The decoder MUST reject, each with its own reason: indefinite-length items, tags, unsupported simple values and floats, non-minimal integer heads, map keys out of canonical order, duplicate map keys, invalid UTF-8, trailing bytes, reserved additional-information values, and input that ends early.
- **CBOR-5.4** A non-minimal head MUST be rejected. Such a head is well-formed under RFC 8949 and is a second encoding of a value that already has one, which is precisely the ambiguity this library exists to remove. Nothing legitimate emits one.
- **CBOR-5.5** Duplicate map keys MUST be rejected. Which of two entries a reader takes is unspecified, so admitting them means two readers can disagree about one document.
- **CBOR-5.6** The error type MUST distinguish every reason in CBOR-5.3, and MUST carry a `name` giving each a short stable string for a log record or a span attribute. "Malformed" in a log ends no investigation.

---

## 6. Canonical form

- **CBOR-6.1** The canonical form is CTAP2's, and it MUST be implemented as stated here rather than as RFC 8949 §4.2.1 states its own. Integers use the shortest head that holds them. Lengths are definite. Map keys are sorted: a lower major type sorts earlier; among keys of the same major type, the shorter encoding sorts earlier; among keys encoding to the same length, the lower byte-wise lexical value sorts earlier.
- **CBOR-6.2** The implementation MUST NOT assume that CBOR-6.1 and RFC 8949's core deterministic ordering agree, and MUST NOT be built by reading RFC 8949 alone. RFC 8949 sorts on the encoded key bytes with no length precedence and names the rule here as a separate, older option. WebAuthn specifies CTAP2's form for attestation objects, so CTAP2's is the one a consumer needs, and an implementer following the more famous document will write the other one.
- **CBOR-6.3** There is one decode, and it enforces CBOR-6.1 inline as it reads. A map whose keys are out of order is refused where the violation is found, rather than recorded and handed back for the caller to judge. No mode, no flag, and no second entry point that tolerates non-canonical input.
- **CBOR-6.4** Enforcing inline means the check reaches every part of a document, including the parts a caller never reads. Getting to the field you want means walking what precedes it, and CBOR-1.1 forbids passing over bytes without understanding them. A consumer reading a WebAuthn attestation object therefore refuses it for a quirk anywhere inside, `attStmt` included, which it decodes only to get past. That cost is accepted; see 13.6.
- **CBOR-6.5** Ordering and duplicate detection are one comparison and MUST be implemented as one. Canonical keys strictly increase, so comparing each key against its predecessor answers both questions at once: greater is well formed, equal is the duplicate of CBOR-5.5, and lower is the violation of CBOR-6.1.

---

## 7. Encoding

- **CBOR-7.1** `encode` MUST be total: every value of the type has an encoding, with no error case and no `Option`.
- **CBOR-7.2** `encode` MUST always emit canonical form, sorting map entries itself. A caller that built a map in a convenient order still gets canonical bytes out, which is what makes the encoder safe to use for a signature input.
- **CBOR-7.3** Because CBOR-7.2 sorts, `encode` is not injective on values that differ only in the order of their map entries. The theorems in §10 MUST account for this rather than being weakened to hide it.
- **CBOR-7.4** `encode` on a value carrying duplicate map keys produces bytes the decoder will reject. A predicate reporting whether a value has distinct keys throughout MUST be provided, so this is a condition a caller can check rather than a trap.
- **CBOR-7.5** Output SHOULD be built without repeated copying of the whole buffer. A nested document should not cost quadratic time in its own size.

---

## 8. Queries

- **CBOR-8.1** Reading a map by integer key and by text key MUST be supported directly, without the caller pattern matching over entries. COSE labels are small integers and this is the library's commonest use.
- **CBOR-8.2** A key that is absent and a key whose value is of the wrong type MUST be distinguishable. "This COSE key has no `-1` label" and "its `-1` label is not a byte string" are different defects with different causes, and an accessor that returns `none` for both leaves the caller unable to say which it met.

---

## 9. Resource bounds

- **CBOR-9.1** The decoder MUST NOT allocate on a declared length before confirming the input actually holds that many bytes. A nine-byte head can declare a byte string of `2^64 - 1`, and a decoder that trusts it is a one-packet denial of service.
- **CBOR-9.2** Nesting depth MUST be bounded, with a default and a way to raise it. Arrays and maps recurse, and input nested ten thousand deep should be refused by name rather than by exhausting the stack.
- **CBOR-9.3** The depth bound MUST NOT make the theorems of §10 vacuous, and each theorem's doc comment MUST say why it does not. A round-trip theorem that holds only for values shallower than the bound is the theorem that was wanted, but it says so only if it says what the bound admits.

---

## 10. Theorems

These MUST be theorems rather than tests. They are finite case analysis over a decidable structure, and a counterexample in any of them is a correctness defect in something signing or verifying bytes.

- **CBOR-10.1** Round trip: for every value, decoding its encoding yields that value with its maps sorted. Stated against a sorting normalisation rather than against the value itself, because of CBOR-7.3.
- **CBOR-10.2** Sorting is idempotent, which is what makes CBOR-10.1 say what it appears to say: a value already sorted round-trips to itself exactly.
- **CBOR-10.3** Uniqueness: if the decode accepts some bytes and yields a value, then encoding that value returns exactly those bytes. This is the theorem that earns the library its purpose, because it makes canonicity a property of the decoder rather than a check every caller has to remember.
- **CBOR-10.4** Minimal heads: every integer, length and key the encoder emits uses the shortest head that holds it.
- **CBOR-10.5** Where a theorem carries a hypothesis that map keys are distinct, its doc comment MUST say why the hypothesis is not doing the work: every value the decoder produces satisfies it, by CBOR-5.5.
- **CBOR-10.6** Each theorem MUST carry a doc comment of two paragraphs. The first says in plain English what it establishes and why that is worth establishing. The second reads the proposition back term by term, saying what each predicate answers true to and what each argument does.

---

## 11. Testing

- **CBOR-11.1** RFC 8949 Appendix A's example table MUST be committed as fixtures and run in both directions. It is the nearest thing this format has to a conformance suite.
- **CBOR-11.2** The Appendix A entries that fall outside the supported subset are tests too, of the rejection path: each MUST be refused, with the reason asserted and not merely the refusal.
- **CBOR-11.3** Real COSE public keys for ES256, RS256 and EdDSA, and at least one real WebAuthn attestation object, MUST be committed as fixtures and decoded. These are what say the library works on its actual input rather than on the specification's examples.
- **CBOR-11.4** Adversarial cases MUST be covered at minimum: a declared length beyond the end of the input; nesting past the depth bound; duplicate keys; a non-minimal head; an indefinite-length item; invalid UTF-8 in a text string; trailing bytes after a complete item; empty input; and a map whose keys are out of canonical order. A map correctly ordered at the top level but not inside a nested value MUST be refused too, since the cost accepted in CBOR-6.4 is only bought if the check really does reach everywhere.
- **CBOR-11.5** The suite MUST need no network and no native dependency, so that `lake test` runs anywhere the toolchain does.
- **CBOR-11.6** `lake build` and `lake test` MUST both pass with no warnings before any task is considered complete. Verify individual files with the Lean LSP diagnostics while working.

---

## 12. Code standards

The package carries its own `CLAUDE.md` recording these, since an agent working here has no other source for them.

- **CBOR-12.1** Every file starts with the copyright statement: `Copyright (c) 2026 Paul Butcher. All rights reserved.` and the Apache 2.0 notice.
- **CBOR-12.2** Comments explain *why*, never restate the code. No file or function header comments unless they add real value. No references to plans, milestones, or rejected designs.
- **CBOR-12.3** Never use an emdash. Use a comma or a semicolon.
- **CBOR-12.4** `partial` is forbidden unless genuinely unavoidable, as is any function that panics on bad input.
- **CBOR-12.5** Never leave `sorry` or an admitted goal. The build treats warnings as errors, which is also why the `plausible` tactic is unusable and any property must be written as an explicit test run.
- **CBOR-12.6** Markdown prose is written one paragraph to a line, never hard-wrapped.
- **CBOR-12.7** No git operations of any kind.

---

## 13. Open decisions

Unresolved unless the entry says otherwise. Each needs an answer before the affected part is built; a recommendation is offered but the decision is not the implementer's to make. Ask, do not assume.

- **13.1 A typeclass and deriving layer.** `lean-json` carries `ToJson` / `FromJson` and a deriving macro in separate targets. The first consumer here reads COSE maps by querying them and needs none of it. Recommendation: out for now, added as its own target when something wants it, so the core stays dependency-free and small.
- **13.2 RFC 8949 core deterministic ordering.** A second canonical mode, selectable, for consumers that are not CTAP2. Recommendation: not yet, but keep the ordering rule in one place so adding it is a parameter rather than a rewrite.
- **13.3 Floats and the remaining simple values.** Needed by anything using this as a general CBOR library rather than as a COSE one. Recommendation: defer, and make sure CBOR-1.1 means the omission is visible rather than silent.
- **13.4 Tags.** None are needed now. Bignums, tags 2 and 3, would be the first to arrive, and they interact with CBOR-4.1's integer representation.
- **13.5 Streaming.** A decoder over a chunked source, for inputs too large to hold. No target consumer has one; a WebAuthn attestation object is a few hundred bytes.
- **13.6 Tolerating non-canonical map ordering.** Answered: not built, which is what CBOR-6.3 records. WebAuthn specifies canonical form, no authenticator is known to violate it, and a tolerance built on that absence would be an unevidenced escape hatch in a library whose entire value is that bytes are a function of the value. Strictness is also self-diagnosing, because a device that does violate it produces a named refusal in a log, and that refusal is the evidence which would justify reopening this. Reopening means a second function whose name says what it surrenders, never a change to what `decode` does. It also means touching the decoder and re-checking the proofs that unfold it, which is the price of enforcing inline rather than reporting, and is accepted.

---

## 14. Suggested delivery order

Each step ends somewhere the build and the tests pass.

1. The value type, the encoder, and the ordering rule of CBOR-6.1.
2. The decoder with its error type, enforcing CBOR-6.1 inline and requiring the whole input.
3. The Appendix A vectors in both directions, including the refusals of CBOR-11.2.
4. The round trip and idempotence theorems, CBOR-10.1 and CBOR-10.2.
5. The uniqueness theorem, CBOR-10.3.
6. `decodePrefix`, the resource bounds of §9, and the adversarial suite.
7. Queries, and the COSE and attestation fixtures.

The theorems come before the bounds deliberately. A depth bound added to a decoder whose round trip is already proved is a hypothesis to discharge; one present from the start tends to be proved around rather than through.
