-- Copyright (c) 2026 the proofbeta authors. All rights reserved. See LICENSE.
import Work.Examples
import Engine.Step
import EngineRevision

/-!
# work-engine

The core's layered engine serving the work layer (`Work.work`), stamped with the revision it is built from
(`EngineRevision.lean`, written by `scripts/stamp_revision` before the build): the binary a work stream's
`proof_revision_url` names.

    work-engine                  serve JSON lines (it starts empty and prints {"ready":true})
    work-engine --self-test      the worked examples through the compiled code
    work-engine --revision       {"revision", "repo"}: the commit it was built from
-/

def main (args : List String) : IO UInt32 :=
  StreamCore.Engine.Layered.mainAt Work.work "work-engine" (pure Work.Examples.allOk)
    StreamCore.Engine.built args
