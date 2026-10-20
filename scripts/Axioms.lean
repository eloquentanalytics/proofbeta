-- Copyright (c) 2026 the proofbeta authors. All rights reserved. See LICENSE.
import Lean
import StreamCore.Interface
import StreamCore.Oracle
import StreamCore.WireState
import Engine.Step
import Work.Examples

/-!
# The axiom check

Every declaration under `StreamCore.*` and `Work.*` (theorems and definitions, those written and those Lean generates,
found in the environment rather than listed by hand) depends on `propext`, `Quot.sound` and `Classical.choice` at
most, so on no `sorryAx` and no axiom of ours. (`Classical.choice` is allowed in proofs: since Lean v4.35 core
`String` lemmas use it. What runs is compiled code, and `scripts/Audit.lean` and the forbidden-word scan check that it
has no `partial`, `unsafe`, `implemented_by`, `extern` or `native_decide` of ours.)

Run: `lake env lean scripts/Axioms.lean` (scripts/check.sh step 2).
-/

open Lean

#eval show CoreM Unit from do
  let env ← getEnv
  let allowed := [``propext, ``Quot.sound, ``Classical.choice]
  for ns in [`StreamCore, `Work] do
    let mut thms := 0
    let mut defs := 0
    let mut bad : Array (Name × Name) := #[]
    for (n, ci) in env.constants.toList do
      if ns.isPrefixOf n && !n.isInternal then
        match ci with
        | .thmInfo _ => thms := thms + 1
        | .defnInfo _ => defs := defs + 1
        | _ => pure ()
        for a in ← collectAxioms n do
          if !allowed.contains a then bad := bad.push (n, a)
    if !bad.isEmpty then
      for (n, a) in bad do IO.println s!"axioms: {n} depends on {a}"
      throwError "a declaration depends on an axiom outside propext, Quot.sound, Classical.choice"
    if thms == 0 then throwError s!"axioms: no theorems found under {ns}"
    IO.println s!"axioms: {ns}: {thms} theorems and {defs} definitions: propext, Quot.sound, Classical.choice at most"
