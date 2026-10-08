/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import Tests.AppendixA
import Tests.Encode
import Tests.Decode
import Tests.Adversarial
import Tests.WebAuthn
import Tests.Proofs.Query
import Tests.Proofs.Prefix

/-!
Theorems pass by compiling. What runs here are the fixtures, whose value is agreement with bytes
no proof could establish.
-/

def checks : List (String × Bool) :=
  Tests.AppendixA.checks ++ Tests.Encode.checks ++ Tests.Decode.checks ++
    Tests.Adversarial.checks ++ Tests.WebAuthn.checks

public def main : IO UInt32 := do
  let checks := checks ++ (← Tests.Adversarial.ioChecks)
  let failed := checks.filter fun (_, passed) => !passed
  for (name, _) in failed do
    IO.eprintln s!"FAILED: {name}"
  if failed.isEmpty then
    IO.println s!"{checks.length} checks passed"
    return 0
  else
    IO.eprintln s!"{failed.length} of {checks.length} checks failed"
    return 1
