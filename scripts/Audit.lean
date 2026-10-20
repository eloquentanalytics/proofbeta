-- Copyright (c) 2026 the proofbeta authors. All rights reserved. See LICENSE.
import Lean
import StreamCore.WireTheorems
import Engine.Step
import Work.Layer

/-!
# Audit of the decision function's dependency tree

That no `partial`, `unsafe`, `implemented_by`, `extern` or `native_decide` of ours is under the decision function is
checked here, by walking declarations, because it is not a proposition of the logic.

Walks every constant that the `roots` below reach (the decision, fast-path, wire and engine functions) (types and values, transitively) and
reports each one that is `unsafe`, `partial` (an opaque whose code is implemented by another), `@[implemented_by]` or
`@[extern]`. It fails when:
- any such constant is in the `StreamCore` or `Work` namespace (our sources must have none); or
- any such constant outside it is not in `trusted` below: core primitives whose compiled code is C (`@[extern]`) or a
  faster equivalent (`@[implemented_by]`), which the kernel does not check against their definitions.
The list is printed, so a toolchain change that adds one is seen in CI.

Run: `lake env lean scripts/Audit.lean` (scripts/check.sh step 4).
-/

open Lean

def roots : List Name :=
  [``StreamCore.handle, ``StreamCore.accept, ``StreamCore.check, ``StreamCore.run,
   ``StreamCore.toEvent, ``StreamCore.rejection, ``StreamCore.ok, ``StreamCore.Past.mayAct,
   ``StreamCore.Wire.stepJ, ``StreamCore.Wire.replayRows, ``StreamCore.Wire.rowFromJ,
   ``StreamCore.Wire.requestFromJ, ``StreamCore.Wire.responseToJ, ``StreamCore.Wire.malformedJ,
   ``StreamCore.Wire.lineJ, ``StreamCore.stepS, ``StreamCore.respondS, ``StreamCore.fold,
   ``StreamCore.Wire.replaySFrom, ``StreamCore.Wire.stateFromJ, ``StreamCore.Wire.stateToJ,
   ``StreamCore.Wire.streamSJ, ``StreamCore.Wire.entryRequest, ``StreamCore.Wire.entrySync,
   -- the services themselves: every field the generic functions call, the core's and any layer's
   ``StreamCore.coreService, ``StreamCore.Layer.service,
   -- the work layer: its commands, rules, guards, memory and reads, and its service
   ``Work.work]

/-- What the unproved edge may reach beyond the proved functions that is unsafe, partial, implemented_by or extern:
the hash map and the primitives of our JSON parser and printer (`Engine/Json.lean`), as of Lean v4.35.0. The audit FAILS if the edge
reaches anything else: a new unproved dependency of the engine must be reviewed and added here. -/
def edgeAllowed : List String := [
  "Array.propagateMark", "Array.replicate", "Array.set", "Array.uget", "Array.uset", "Int.add", "Int.decLe",
  "Int.decNonneg", "Int.mul", "Int.neg", "Int.negSucc", "Int.ofNat", "Int.sub", "Nat.repr", "Nat.xor",
  "String.decidableLT", "String.hash", "String.push", "System.Platform.getNumBits", "UInt64.mod", "UInt64.ofBitVec",
  "UInt64.ofNat", "UInt64.shiftRight", "UInt64.toBitVec", "UInt64.toNat", "UInt64.toUSize", "UInt64.xor",
  "USize.land", "USize.ofBitVec", "USize.ofNat", "USize.sub", "USize.toBitVec", "USize.toNat"]

/-- The unproved edge: bytes to `J` and back (our own parser and printer, `Engine/Json.lean`), and the engine's map
from streams to entries, for any service (`Engine.step S`, the same code for the core and for every layer). Walked: it
may reach only what `edgeAllowed` lists, no panic, and nothing of Lean's JSON library or `Parsec`. (`Engine.serveAt`,
the IO loop around `Engine.stepLineAt`, is not walked: it reaches the IO primitives.) -/
def edge : List Name := [``StreamCore.Wire.parseLine, ``StreamCore.Wire.render,
  ``StreamCore.Engine.step, ``StreamCore.Engine.stepLine, ``StreamCore.Engine.stepLineAt]

/-- Constants through which compiled code can panic. None may be reachable from the roots or the edge. -/
def panics : List Name := [``panic, ``panicCore, ``panicWithPos, ``panicWithPosWithDecl, ``outOfBounds]

partial def closure (env : Environment) (todo : List Name) (seen : NameSet) : NameSet :=
  match todo with
  | [] => seen
  | n :: rest =>
    if seen.contains n then closure env rest seen else
    match env.find? n with
    | none => closure env rest (seen.insert n)
    | some ci =>
      let used := ci.type.getUsedConstants ++ (ci.value?.map (·.getUsedConstants) |>.getD #[])
      closure env (used.toList ++ rest) (seen.insert n)

/-- Core primitives with compiled implementations that the kernel does not check (as of Lean v4.35.0). Since v4.35 a
`String` is a `ByteArray` of UTF-8 and `String.all`, `String.drop` and their kin run on `String.Slice` patterns, whose
search loops are `WellFounded.extrinsicFix` (compiled as plain recursion, termination not checked by the kernel). -/
def trusted : List String := [
  "Array.emptyWithCapacity", "Array.foldlM", "Array.getInternal", "Array.mk", "Array.push", "Array.size",
  "Array.toList", "ByteArray.copySlice", "ByteArray.data", "ByteArray.emptyWithCapacity", "ByteArray.get",
  "ByteArray.mk", "ByteArray.push", "ByteArray.size", "Char.ofNatAux", "Lean.Name.anonymous", "Lean.Name.str",
  "Nat.add", "Nat.beq", "Nat.ble", "Nat.decEq", "Nat.decLe", "Nat.decLt", "Nat.div", "Nat.land", "Nat.lor",
  "Nat.mod", "Nat.modCore", "Nat.mul", "Nat.pow", "Nat.pred", "Nat.shiftLeft", "Nat.shiftRight", "Nat.sub",
  "String.Pos.Raw.atEnd", "String.Pos.Raw.extract", "String.Pos.Raw.get", "String.Pos.Raw.next", "String.append",
  "String.decEq", "String.decidableLT", "String.decodeChar", "String.extract", "String.getUTF8Byte", "String.length", "String.ofByteArray",
  "String.ofList", "String.toByteArray", "String.toList", "String.utf8ByteSize", "UInt32.decEq", "UInt32.decLe",
  "UInt32.decLt", "UInt32.lor", "UInt32.mod", "UInt32.ofBitVec", "UInt32.ofNat", "UInt32.ofNatLT",
  "UInt32.shiftLeft", "UInt32.toBitVec", "UInt32.toNat", "UInt8.decEq", "UInt8.land", "UInt8.ofBitVec",
  "UInt8.ofNat", "UInt8.toBitVec", "UInt8.toNat", "UInt8.toUInt32", "WellFounded.extrinsicFix",
  "WellFounded.extrinsicFix₃", "_private.Init.Data.Iterators.Basic.0.Std.Internal.idOpaque",
  "_private.Init.WFExtrinsicFix.0.WellFounded.opaqueFix"]

def flags (env : Environment) (n : Name) : List String :=
  let ci? := env.find? n
  (if ci?.map (·.isUnsafe) |>.getD false then ["unsafe"] else []) ++
  (if isExtern env n then ["extern"] else []) ++
  (if (Compiler.getImplementedBy? env n).isSome then ["implemented_by"] else []) ++
  (match ci? with | some (.opaqueInfo _) => ["opaque"] | _ => [])

#eval show CoreM Unit from do
  let env ← getEnv
  let all := closure env roots {}
  let mut ours := 0
  let mut bad : Array String := #[]
  let mut found : Array String := #[]
  for n in all.toList do
    let isOurs := (`StreamCore).isPrefixOf n || (`Work).isPrefixOf n
    if isOurs then ours := ours + 1
    let fs := flags env n
    if fs.isEmpty then continue
    let line := s!"{n} [{", ".intercalate fs}]"
    found := found.push line
    if isOurs then bad := bad.push s!"ours: {line}"
    else if !trusted.contains n.toString then bad := bad.push s!"not in the trusted list: {line}"
  IO.println s!"audit: {all.size} constants reached from {roots.length} roots, {ours} of them in StreamCore or Work"
  for l in found.qsort (· < ·) do IO.println s!"  trusted primitive: {l}"
  for p in panics do
    if all.contains p then bad := bad.push s!"reaches {p}: compiled code could panic"
  if !bad.isEmpty then
    throwError s!"audit failed: {bad}"
  IO.println "audit: no unsafe, partial, implemented_by or extern constant in StreamCore or Work; no panic reachable"
  -- The walk above is over kernel definitions. The compiler instead runs `@[csimp]` replacements
  -- (each one proved equal to what it replaces by its own theorem, but applied by the unverified compiler) and the
  -- `@[extern]` primitives listed above. Here are the csimp replacements the compiled decision functions use.
  let cs := Lean.Compiler.CSimp.ext.getState env
  let mut csimps : Array String := #[]
  for n in all.toList do
    if let some r := cs.map.find? n then csimps := csimps.push s!"{n} ~> {r.toDeclName}"
  for l in csimps.qsort (· < ·) do IO.println s!"  csimp: {l}"
  -- As of Lean v4.35.0.
  let pinned := ["Acc.rec", "Bool.and", "Bool.not", "Bool.or", "ByteArray.append", "List.append", "List.filter",
    "List.filterMap", "List.flatMap", "List.flatten", "List.length", "List.map", "Nat.rec", "List.take", "String.Slice.Pos.next",
    "String.utf8EncodeChar", "WellFounded.fix", "WellFounded.fixF"]
  for n in all.toList do
    if (cs.map.find? n).isSome && !pinned.contains n.toString then
      throwError s!"audit failed: a new @[csimp] replacement for {n}: review it and add it to the pinned list"
  IO.println s!"audit: {csimps.size} @[csimp] replacements in the compiled decision functions (trusted)"
  let outside := closure env edge {}
  let mut odd : Array String := #[]  -- flagged constants the edge reaches beyond the proved functions
  for n in outside.toList do
    let fs := flags env n
    if !fs.isEmpty && !(all.contains n) then odd := odd.push s!"{n}"
  for o in odd.qsort (· < ·) do
    if !edgeAllowed.contains o then
      throwError s!"audit failed: the unproved edge reaches {o}, which is not in edgeAllowed: review it"
  for p in panics do
    if outside.contains p then throwError s!"audit failed: the unproved edge reaches {p}: compiled code could panic"
  for n in outside.toList do
    let s := n.toString  -- private names too (`_private.Lean.Data.Json...`)
    if (s.splitOn "Lean.Json").length > 1 || (s.splitOn "Lean.Data.Json").length > 1 || (s.splitOn "Parsec").length > 1 then
      throwError s!"audit failed: the unproved edge reaches {n}: the JSON edge is ours, not Lean's library"
  IO.println s!"audit: the unproved edge (parseLine, render, Engine.step) reaches {outside.size} constants, {odd.size} of them unsafe, partial, implemented_by or extern beyond the proved functions'; no panic, no Lean.Json or Parsec"
