-- Copyright (c) 2026 the proofbeta authors. All rights reserved. See LICENSE.
import Engine.Json

/-! The specification path as an executable (`spec-engine`), for differential testing against the fast-path engine
(`stream-engine`). One global log over every stream; each line is `Wire.lineJ` (requests through `stepJ` = `handle`
on the whole log, reads through the log-based `streamJ`). `{"reset":true}` empties the log. -/
open StreamCore StreamCore.Wire

def main : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  let mut log : Log := []
  repeat
    let line ← stdin.getLine
    if line.isEmpty then break
    let line := line.trimAsciiEnd.copy
    if line.isEmpty then continue
    match parseLine line with
    | .error d => stdout.putStrLn (render (malformedJ d))
    | .ok (.obj [("reset", .bool true)]) => log := []; stdout.putStrLn (render (.obj [("reset", .bool true)]))
    | .ok j =>
      let (log', out) := lineJ log j
      log := log'
      stdout.putStrLn (render out)
    stdout.flush
