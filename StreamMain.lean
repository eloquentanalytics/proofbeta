-- Copyright (c) 2026 the proofbeta authors. All rights reserved. See LICENSE.
import Engine.Step
import StreamCore.Oracle
import EngineRevision

/-!
# stream-engine

A long-lived process speaking JSON lines on stdin and stdout.

    stream-engine                  serve (it starts empty and prints {"ready":true})
    stream-engine --self-test      run the worked examples through the compiled code
    stream-engine --revision       print the revision it was built from: {"revision", "repo"}

The revision is `EngineRevision.lean`'s, which `scripts/stamp_revision` writes from git before the build (it is not in
git: a commit cannot name its own hash). Served, `{"query":"revision"}` answers it too.

The messages, the per-stream state and the serving loop are `Engine/Step.lean`'s, over `coreService`; the loop is
unproved (`Theorems.lean`, "Not proved here").
-/

open StreamCore StreamCore.Wire

def fail (msg : String) : IO UInt32 := do
  IO.eprintln s!"stream-engine: {msg}"
  return 2

/-- The worked examples, through the compiled code (the `#guard`s run them in the interpreter at build time). -/
def selfTest : IO UInt32 := do
  let bad := StreamCore.Examples.cases.filter fun (log, e, want) =>
    rejection log e != want || rejectionS (fold e.stream log) e != want
  let badChecks := StreamCore.Examples.validLogs.filter (!check ·)
  let badRun := !StreamCore.Examples.commandsProduceEvents
  let badJson := !(sampleRequests.all roundTripRequest && eventsRoundTrip && badLines.all refuses)
  if bad.isEmpty && badChecks.isEmpty && !badRun && !badJson then
    IO.println s!"self-test: {StreamCore.Examples.cases.length} cases (rules and fast path), {StreamCore.Examples.validLogs.length} valid logs, run, json: ok"
    return 0
  else
    fail s!"self-test failed: {bad.length} cases, {badChecks.length} valid logs, run {badRun}, json {badJson}"

def main (args : List String) : IO UInt32 := do
  match args with
  | ["--self-test"] => selfTest
  | ["--revision"] =>
    IO.println (render (StreamCore.Engine.revisionJ StreamCore.Engine.built))
    return 0
  | [] =>
    StreamCore.Engine.serveStdioAt coreService StreamCore.Engine.built (← IO.getStdout)
    return 0
  | _ => fail "usage: stream-engine | stream-engine --self-test | stream-engine --revision"
