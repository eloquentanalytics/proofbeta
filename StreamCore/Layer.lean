-- Copyright (c) 2026 the proofbeta authors. All rights reserved. See LICENSE.
import StreamCore.Streams

/-!
# A layer: commands and events added on top of a base, without changing it

A `Layer B` is what an extension writes on a base `B` (the core, `coreBase`, by default; or a layer with everything
below it, `Layer.toBase`), in four parts:
- its commands and events (`Layer.Commands`): the two types, the event's request and back (two equations, proved by
  `layer_bijection`), the stream a command is on, and each command's wire form as a schema (`CmdSchema`: a name and
  fields of a few kinds) with the command as that schema's values and back (one equation, `layer_bijection`; and each
  command under one of the schema's names, `layer_names`);
- what its rules remember of the stream's own layer events (`Memory`), with its fast path: the facts the events
  stated (`Memory.facts`), or a layer's own (recipes: a register, retractable facts, records);
- its rules (`Layer.Rule`), tried in order, each reading the base's `View` of the event's stream and the memory;
- its guards (rules over the base's events, default none), tried after the base's own rules on the base's events: a
  layer may add commands and events and tighten the base's commands, never loosen them or change what the base's
  events mean.

Everything else is derived and proved once, here, for every layer on every base: the actor, stream and translation of
an event (a layer command mints nothing, so any fresh id is refused with `fresh_ids`), the command, event, request and
state codecs and their round trips, the names check, the rules' locality and the fast path. From them this file builds
the combined service, `Layer.service L : Service` (the base's events and the layer's side by side), so `Service.lean`
gives it what the core has: the decision is local, the fast path is the specification, batches and compare-and-set
appends refine `run`, stored rows round trip, and the engine's bookkeeping is proved. And a layer cannot break what
is below it: the base's events of a valid combined log form a valid log of the base (`ValidX.base`; at the core,
`ValidX.cores`), each layer event held every layer rule at its point (`ValidX.holds`, `ValidX.holdsNamed`), and each
base event held every guard (`ValidX.guardHolds`, `ValidX.guardHoldsNamed`).

Layers compose two ways. A tower: `L.toBase` is a base, so a layer sits on a layer, and `h.base.base` takes a valid
log two levels down. A sum: `L₁.sum L₂` is two independent layers on one base side by side, and each side of a valid
sum is valid alone (`ValidX.left`, `ValidX.right`).
-/

namespace StreamCore
open StreamCore.Wire

/-! ## The core's names, so a layer can avoid them -/

def coreCommandNames : List String :=
  ["stream.create", "principal.invite", "principal.promote", "principal.demote", "principal.ban", "stream.panic"]

/-- The string under key `k` of a JSON object, if there is one. -/
def Wire.keyStr (k : String) : J → Option String
  | .obj kvs => match get? kvs k with
    | some (.str n) => some n
    | _ => none
  | _ => none

/-- The object names one of `names` under key `k`. -/
def Wire.hasName (k : String) (names : List String) (j : J) : Bool :=
  match keyStr k j with
  | some n => names.contains n
  | none => false

theorem Wire.commandToJ_name (cmd : Command) : ∃ n, keyStr "command" (commandToJ cmd) = some n ∧ n ∈ coreCommandNames := by
  cases cmd <;> simp [commandToJ, changeCommandJ, keyStr, get?, List.find?, coreCommandNames]

theorem Wire.eventToJ_name (e : Event) : ∃ n, keyStr "event" (eventToJ e) = some n ∧ n ∈ coreCommandNames := by
  cases e <;> simp [eventToJ, changeEventJ, keyStr, get?, List.find?, coreCommandNames]

/-! ## A layer's commands and events on the wire, by schema -/

/-- The kind of a command's field: a canonical UUID, a string without U+0000 that `wf` accepts, or the optional
`meta` (`wfMeta`). -/
inductive Kind where
  | uuid
  | str (wf : String → Bool)
  | metaOpt

/-- A field's value. -/
inductive Val where
  | s (x : String)
  | m (x : Meta)
  deriving DecidableEq

/-- One command of a layer on the wire: its name (its event's too) and its fields, in order. Its event's object is
the name under `event`, the `actor`, then the same fields. -/
structure CmdSchema where
  name : String
  fields : List (String × Kind)

/-- The value has the field's kind and form. -/
def Kind.wf : Kind → Val → Bool
  | .uuid, .s x => validUuid x
  | .str wf, .s x => noNul x && wf x
  | .metaOpt, .m o => wfMeta o
  | _, _ => false

/-- One value per field, each of the field's kind and form. -/
def valsWf : List (String × Kind) → List Val → Bool
  | [], [] => true
  | (_, k) :: fs, v :: vs => k.wf v && valsWf fs vs
  | _, _ => false

def Val.toJ : Val → J
  | .s x => .str x
  | .m o => metaJ o

/-- A field of the object `kvs`, read as the core reads its own (`str`, `metaOf`), with the core's messages. -/
def Kind.fromJ (what : String) (kvs : Fields) : String × Kind → Except String Val
  | (k, .metaOpt) => match get? kvs k with
    | none | some .null => .ok (.m none)
    | some (.str s) => .ok (.m (some s))
    | some _ => .error s!"{what}.{k}: expected a string or null"
  | (k, _) => .s <$> Wire.str what kvs k

def valsToJ : List (String × Kind) → List Val → Fields
  | (k, _) :: fs, v :: vs => (k, v.toJ) :: valsToJ fs vs
  | _, _ => []

/-- A layer's object: its name under `what` (`command` or `event`), then its fields. -/
def objToJ (what n : String) (fs : List (String × Kind)) (vs : List Val) : J :=
  .obj ((what, .str n) :: valsToJ fs vs)

/-- Read a layer's object: its name, then the `extra` fields and its schema's, in order. -/
def objFromJ (schema : List CmdSchema) (what : String) (extra : List (String × Kind)) (j : J) :
    Except String (String × List Val) := do
  let kvs ← fields what j
  let n ← str what kvs what
  let some sc := schema.find? (·.name == n) | throw s!"{what}: unknown {what} {n}"
  onlyKeys what kvs (what :: (extra ++ sc.fields).map (·.1))
  return (n, ← (extra ++ sc.fields).mapM (Kind.fromJ what kvs))

/-- A schema a layer may use: none of its names is the core's, and each command's and event's keys are distinct. -/
def schemaOk (schema : List CmdSchema) : Bool :=
  coreCommandNames.all (!(schema.map (·.name)).contains ·) && schema.all fun sc =>
    decide (("command" :: sc.fields.map (·.1)).Nodup) && decide (("event" :: "actor" :: sc.fields.map (·.1)).Nodup)

theorem get?_of_mem {kvs : Fields} {k : String} {j : J} (hn : (kvs.map (·.1)).Nodup) (h : (k, j) ∈ kvs) :
    get? kvs k = some j := by
  induction kvs with
  | nil => cases h
  | cons kv kvs ih =>
    obtain ⟨k', j'⟩ := kv
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hn
    rcases List.mem_cons.mp h with h | h
    · cases h; simp [get?]
    · have hne : k' ≠ k := fun e => hn.1 ⟨(k, j), h, e.symm ▸ rfl⟩
      simpa [get?, List.find?_cons, hne] using ih hn.2 h

theorem valsWf_keys {fs : List (String × Kind)} {vs : List Val} (h : valsWf fs vs = true) :
    (valsToJ fs vs).map (·.1) = fs.map (·.1) := by
  induction fs generalizing vs with
  | nil => rfl
  | cons f fs ih => cases vs <;> simp_all [valsWf, valsToJ]

theorem mapM_fromJ {what : String} {kvs : Fields} {fs : List (String × Kind)} {vs : List Val}
    (hf : valsWf fs vs = true) (hk : ∀ kv ∈ valsToJ fs vs, get? kvs kv.1 = some kv.2) :
    fs.mapM (Kind.fromJ what kvs) = .ok vs := by
  induction fs generalizing vs with
  | nil => cases vs <;> simp_all [valsWf, pure, Except.pure]
  | cons f fs ih => cases vs with
    | nil => simp [valsWf] at hf
    | cons v vs =>
      obtain ⟨k, kd⟩ := f
      simp only [valsWf, valsToJ, Bool.and_eq_true, List.mem_cons, forall_eq_or_imp] at hf hk
      have hrest := ih hf.2 hk.2
      cases kd <;> cases v <;> simp_all [Kind.wf, Kind.fromJ, List.mapM_cons, str, Val.toJ, bind, Except.bind,
        pure, Except.pure, Functor.map, Except.map] <;> (rename_i o; cases o <;> rfl)

theorem objFromJ_toJ {schema : List CmdSchema} {what n : String} {extra : List (String × Kind)} {sc : CmdSchema}
    {vs : List Val} (hsc : schema.find? (·.name == n) = some sc) (hwf : valsWf (extra ++ sc.fields) vs = true)
    (hnd : (what :: (extra ++ sc.fields).map (·.1)).Nodup) :
    objFromJ schema what extra (objToJ what n (extra ++ sc.fields) vs) = .ok (n, vs) := by
  have hkeys : ((what, J.str n) :: valsToJ (extra ++ sc.fields) vs).map (·.1) = what :: (extra ++ sc.fields).map (·.1) := by
    simp [valsWf_keys hwf]
  have hfind : List.find? (fun kv => !(what :: (extra ++ sc.fields).map (·.1)).contains kv.1)
      ((what, J.str n) :: valsToJ (extra ++ sc.fields) vs) = none :=
    List.find?_eq_none.mpr fun kv h => by
      have hc : (what :: (extra ++ sc.fields).map (·.1)).contains kv.1 = true :=
        List.elem_iff.mpr (hkeys ▸ List.mem_map_of_mem h)
      rw [hc]; decide
  simp only [objFromJ, objToJ, fields, str, get?, List.find?_cons, beq_self_eq_true, Option.map_some, hsc, onlyKeys,
    hfind, bind, Except.bind, pure, Except.pure,
    mapM_fromJ hwf fun kv h => get?_of_mem (hkeys ▸ hnd) (List.mem_cons_of_mem _ h)]

/-! ## A layer's commands and events -/

/-- Proves a layer's translation equations (`Layer.Commands`), each by cases and `rfl`. -/
macro "layer_bijection" : tactic =>
  `(tactic| first | (intro x; cases x <;> rfl) | (intro ⟨_, x⟩; cases x <;> rfl))

/-- Proves that every command is on the wire under one of its schema's names (`Layer.Commands.toVals_name`), by cases
and `simp`. -/
macro "layer_names" : tactic =>
  `(tactic| (intro x; cases x <;> simp))

/-- A request of a layer: caller, command, fresh ids (a layer command takes none). -/
abbrev LRequest (Cmd : Type) := Id × Cmd × Fresh

/-- A layer's commands and events: an event is its actor and its command (`toRequest`, `ofRequest`, inverse to each
other); a command is on one stream (`stream`) and is on the wire as the values of its schema (`toVals`, `ofVals`). -/
structure Layer.Commands where
  Cmd : Type
  Ev : Type
  [decEv : DecidableEq Ev]
  toRequest : Ev → Id × Cmd
  ofRequest : Id × Cmd → Ev
  stream : Cmd → Id
  schema : List CmdSchema
  toVals : Cmd → String × List Val
  ofVals : String → List Val → Option Cmd
  ofRequest_toRequest : ∀ e, ofRequest (toRequest e) = e := by layer_bijection
  toRequest_ofRequest : ∀ r, toRequest (ofRequest r) = r := by layer_bijection
  ofVals_toVals : ∀ c, ofVals (toVals c).1 (toVals c).2 = some c := by layer_bijection
  schema_ok : schemaOk schema = true := by decide
  /-- Every command is on the wire under one of the schema's names. -/
  toVals_name : ∀ c, (schema.map (·.name)).contains (toVals c).1 = true := by layer_names

attribute [instance] Layer.Commands.decEv

namespace Layer.Commands
variable (C : Layer.Commands)

/-- The stream a layer event is on: its command's. -/
def evStream (e : C.Ev) : Id := C.stream (C.toRequest e).2

/-- On a concrete layer (`simp` sees its commands as a structure literal) the stream of an event is its command's:
`simp` reduces `L.evStream (.done a t i m)` to `t`. Over a variable layer it does not fire, so `L.evStream x` stays. -/
@[simp] theorem evStream_mk {Cmd Ev : Type} [DecidableEq Ev] {toRequest : Ev → Id × Cmd} {ofRequest : Id × Cmd → Ev}
    {stream : Cmd → Id} {schema toVals ofVals h₁ h₂ h₃ h₄ h₅} (e : Ev) :
    evStream ⟨Cmd, Ev, toRequest, ofRequest, stream, schema, toVals, ofVals, h₁, h₂, h₃, h₄, h₅⟩ e =
      stream (toRequest e).2 := rfl

def names : List String := C.schema.map (·.name)

def fieldsOf (n : String) : List (String × Kind) := ((C.schema.find? (·.name == n)).map (·.fields)).getD []

/-- A well-formed command: its values fit its schema's fields, in kind and form. -/
def cmdWf (cmd : C.Cmd) : Bool :=
  match C.schema.find? (·.name == (C.toVals cmd).1) with
  | some sc => valsWf sc.fields (C.toVals cmd).2
  | none => false

def requestWf : LRequest C.Cmd → Bool
  | (c, cmd, f) => validUuid c && C.cmdWf cmd && f.all validUuid

/-- A well-formed event: the same forms, through the request it came from. -/
def evWf (e : C.Ev) : Bool := C.requestWf ((C.toRequest e).1, (C.toRequest e).2, [])

def cmdToJ (cmd : C.Cmd) : J := objToJ "command" (C.toVals cmd).1 (C.fieldsOf (C.toVals cmd).1) (C.toVals cmd).2

/-- An event: its name, its actor, its command's fields. -/
def evToJ (e : C.Ev) : J :=
  let (n, vs) := C.toVals (C.toRequest e).2
  objToJ "event" n (("actor", .uuid) :: C.fieldsOf n) (.s (C.toRequest e).1 :: vs)

def cmdFromJ (j : J) : Except String C.Cmd := do
  let (n, vs) ← objFromJ C.schema "command" [] j
  let some cmd := C.ofVals n vs | throw s!"command: {n}: unexpected fields"
  checked "command" C.cmdWf cmd

def evFromJ (j : J) : Except String C.Ev := do
  let (n, vs) ← objFromJ C.schema "event" [("actor", .uuid)] j
  let .s a :: vs := vs | throw s!"event: {n}: unexpected fields"
  let some cmd := C.ofVals n vs | throw s!"event: {n}: unexpected fields"
  checked "event" C.evWf (C.ofRequest (a, cmd))

variable {C}

theorem cmdWf_find {cmd : C.Cmd} (h : C.cmdWf cmd = true) : ∃ sc, C.schema.find? (·.name == (C.toVals cmd).1) = some sc ∧
    valsWf sc.fields (C.toVals cmd).2 = true ∧ C.fieldsOf (C.toVals cmd).1 = sc.fields := by
  unfold cmdWf at h
  split at h
  · rename_i sc hsc; exact ⟨sc, hsc, h, by simp [fieldsOf, hsc]⟩
  · cases h

theorem schema_nodup {sc : CmdSchema} (h : sc ∈ C.schema) : ("command" :: sc.fields.map (·.1)).Nodup ∧
    ("event" :: "actor" :: sc.fields.map (·.1)).Nodup := by
  have := C.schema_ok
  simp only [schemaOk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at this
  exact this.2 sc h

theorem cmdFromJ_toJ (cmd : C.Cmd) (h : C.cmdWf cmd = true) : C.cmdFromJ (C.cmdToJ cmd) = .ok cmd := by
  obtain ⟨sc, hsc, hwf, hfs⟩ := cmdWf_find h
  have := objFromJ_toJ (extra := []) hsc hwf (schema_nodup (List.mem_of_find?_eq_some hsc)).1
  simp only [List.nil_append] at this
  simp only [cmdFromJ, cmdToJ, hfs, this, C.ofVals_toVals, checked_ok h, bind, Except.bind]

theorem evFromJ_toJ (e : C.Ev) (h : C.evWf e = true) : C.evFromJ (C.evToJ e) = .ok e := by
  have hc : C.cmdWf (C.toRequest e).2 = true := by simp_all [evWf, requestWf]
  obtain ⟨sc, hsc, hwf, hfs⟩ := cmdWf_find hc
  have := objFromJ_toJ (extra := [("actor", .uuid)]) (vs := .s (C.toRequest e).1 :: (C.toVals (C.toRequest e).2).2)
    hsc (by simp_all [valsWf, Kind.wf, evWf, requestWf]) (schema_nodup (List.mem_of_find?_eq_some hsc)).2
  simp only [evFromJ, evToJ, hfs, List.cons_append, List.nil_append] at this ⊢
  simp only [this, C.ofVals_toVals, C.ofRequest_toRequest, checked_ok h, bind, Except.bind]

theorem cmdFromJ_wf {j : J} {cmd : C.Cmd} (h : C.cmdFromJ j = .ok cmd) : C.cmdWf cmd = true := by
  unfold cmdFromJ at h
  simp only [bind, Except.bind] at h
  repeat (first | (split at h <;> try contradiction) | exact checked_wf h)

theorem evFromJ_wf {j : J} {e : C.Ev} (h : C.evFromJ j = .ok e) : C.evWf e = true := by
  unfold evFromJ at h
  simp only [bind, Except.bind] at h
  repeat (first | (split at h <;> try contradiction) | exact checked_wf h)

theorem hasName_toJ {what : String} {n : String} {fs : List (String × Kind)} {vs : List Val} {sc : CmdSchema}
    (hsc : C.schema.find? (·.name == n) = some sc) : hasName what C.names (objToJ what n fs vs) = true := by
  have hm := List.mem_of_find?_eq_some hsc
  have hn : sc.name = n := by simpa using List.find?_some hsc
  simp only [hasName, keyStr, objToJ, get?, List.find?_cons, beq_self_eq_true, Option.map_some, names]
  simpa [List.contains_iff_mem] using ⟨sc, hm, hn⟩

theorem toVals_mem (cmd : C.Cmd) : C.names.contains (C.toVals cmd).1 = true := C.toVals_name cmd

theorem names_core : coreCommandNames.all (!C.names.contains ·) = true := by
  have := C.schema_ok
  simp only [schemaOk, Bool.and_eq_true] at this
  exact this.1

end Layer.Commands

/-! ## What a layer's rules remember of the stream's own layer events -/

/-- What a layer's rules read of the layer events before the candidate on its stream (`read`), and the state the fast
path keeps instead: folding those events into the state and taking its `view` is reading them (`fold_view`). -/
structure Memory (Ev : Type) where
  V : Type
  read : List Ev → V
  St : Type
  [decSt : DecidableEq St]
  init : St
  step : St → Ev → St
  view : St → V
  fold_view : ∀ past, view (past.foldl step init) = read past
  stateToJ : St → J
  stateFromJ : J → Except String St
  stateFromJ_toJ : ∀ st, stateFromJ (stateToJ st) = .ok st

attribute [instance] Memory.decSt

/-- A fact a layer event states: a name and a key (`("created", work id)`). -/
abbrev Fact := String × String

/-- Add a fact unless it is there: the facts, in order of first mention. -/
def addFact (st : List Fact) (x : Fact) : List Fact := if st.contains x then st else st ++ [x]

theorem contains_foldl_addFact (ms st : List Fact) (x : Fact) :
    (ms.foldl addFact st).contains x = (st.contains x || ms.contains x) := by
  induction ms generalizing st with
  | nil => simp
  | cons y ys ih =>
    simp only [List.foldl_cons, ih, addFact]
    split <;> rename_i h <;> by_cases hx : x = y <;> simp_all

theorem facts_fold {Ev : Type} (marks : Ev → List Fact) (past : List Ev) (st : List Fact) (x : Fact) :
    (past.foldl (fun st e => (marks e).foldl addFact st) st).contains x =
      (st.contains x || past.any fun e => (marks e).contains x) := by
  induction past generalizing st with
  | nil => simp
  | cons e es ih => simp only [List.foldl_cons, List.any_cons, ih, contains_foldl_addFact, Bool.or_assoc]

theorem facts_view {Ev : Type} (marks : Ev → List Fact) (past : List Ev) :
    (fun f k => (past.foldl (fun st e => (marks e).foldl addFact st) []).contains (f, k)) =
      fun f k => past.any fun e => (marks e).contains (f, k) := by
  funext f k; simpa using facts_fold marks past [] (f, k)

def factsToJ (st : List Fact) : J := .arr (st.map fun (f, k) => .arr [.str f, .str k])

def factsFromJ : J → Except String (List Fact)
  | .arr xs => xs.mapM fun
    | .arr [.str f, .str k] => .ok (f, k)
    | _ => .error "state: expected a fact"
  | _ => .error "state: expected facts"

theorem factsFromJ_toJ (st : List Fact) : factsFromJ (factsToJ st) = .ok st := by
  induction st with
  | nil => rfl
  | cons x xs ih =>
    simp only [factsToJ, factsFromJ, List.map_cons, List.mapM_cons] at ih ⊢
    simp [ih, bind, Except.bind, pure, Except.pure]

/-- **Facts**: the rules read whether some layer event before the candidate on its stream stated fact `f` of key `k`
(`seen f k`); the state is the facts stated, in order of first mention. `marks e`: the facts event `e` states. -/
def Memory.facts {Ev : Type} (marks : Ev → List Fact) : Memory Ev where
  V := String → String → Bool
  read past f k := past.any fun e => (marks e).contains (f, k)
  St := List Fact
  init := []
  step st e := (marks e).foldl addFact st
  view st f k := st.contains (f, k)
  fold_view := facts_view marks
  stateToJ := factsToJ
  stateFromJ := factsFromJ
  stateFromJ_toJ := factsFromJ_toJ

/-- The keys of fact `f` in a facts state, in order of first mention (for reads). -/
def factKeys (st : List Fact) (f : String) : List String := st.filterMap fun (f', k) => if f' == f then some k else none

namespace Memory
variable {Ev : Type}

/-- `Memory.facts` reads whether some event stated the fact. -/
@[simp] theorem facts_read (marks : Ev → List Fact) (past : List Ev) (f k : String) :
    (Memory.facts marks).read past f k = past.any fun e => (marks e).contains (f, k) := rfl

end Memory

/-! ## A valid log, projected: superposition refinement -/

/-- **Projection keeps validity.** If every event a service `S` accepts projects (by `f`) to nothing or to an event
that service `T` accepts against the projection of the log, the projection of every valid log of `S` is a valid log
of `T`. The layer's guarantees below (`ValidX.base`, `ValidX.left`, `ValidX.right`) are this, each at its `f`. -/
theorem Service.Valid.project {S T : Service} (f : S.Ev → Option T.Ev)
    (hok : ∀ log e, S.Valid log → S.ok log e = true → ∀ e', f e = some e' → T.ok (log.filterMap f) e' = true)
    {log : S.Log} (h : S.Valid log) : T.Valid (log.filterMap f) := by
  induction h with
  | nil => exact .nil
  | @snoc log e hv hk ih =>
    rw [List.filterMap_append]
    cases hf : f e with
    | none => simpa [hf] using ih
    | some e' => simpa [hf] using Service.Valid.snoc ih (hok log e hv hk e' hf)

/-! ## A base: a service, and the facts it shows the layer above -/

/-- The name of the command a request carries: the `command` key of its `command` object. -/
def Wire.cmdName : J → Option String
  | .obj kvs => (get? kvs "command").bind (keyStr "command")
  | _ => none

theorem Wire.keyStr_objToJ (what n : String) (fs : List (String × Kind)) (vs : List Val) :
    keyStr what (objToJ what n fs vs) = some n := by
  simp [keyStr, objToJ, get?]

/-- What a layer sits on: a service (the core, or a layer with everything below it, `Layer.toBase`), and what its
layers' rules and guards may read of a stream (`View`):
- `view log t`: the view of stream `t` after `log`, which reads only `t`'s events (`view_local`), and which the fast
  path reads from the stream's state (`viewS`, `viewS_fold`);
- `live st`: the stream exists, so a read of it shows the layers' fields;
- `names`: the names its commands and events are on the wire under (each request's and each event's,
  `requestToJ_name`, `eventToJ_name`), which no layer above may use. -/
structure Base extends Service where
  View : Type
  view : List Ev → Id → View
  view_local : ∀ log s, view (log.filter (stream · == s)) s = view log s
  viewS : St → View
  viewS_fold : ∀ s (log : List Ev), viewS (log.foldl step (init s)) = view log s
  live : St → Bool
  names : List String
  requestToJ_name : ∀ r, ∃ n, cmdName (requestToJ r) = some n ∧ n ∈ names
  eventToJ_name : ∀ e, ∃ n, keyStr "event" (eventToJ e) = some n ∧ n ∈ names

/-- **The core, as a base**: its view is `Past.view`, read from the state by `StreamState.view`. -/
abbrev coreBase : Base where
  toService := coreService
  View := StreamCore.View
  view log t := Past.view log t
  view_local log s := view_onStream log s
  viewS := StreamState.view
  viewS_fold s log := fold_view s log
  live st := st.created
  names := coreCommandNames
  requestToJ_name := fun ⟨c, cmd, f⟩ => by
    obtain ⟨n, h1, h2⟩ := commandToJ_name cmd
    exact ⟨n, by simpa [cmdName, requestToJ, get?] using h1, h2⟩
  eventToJ_name := eventToJ_name

@[simp] theorem coreBase_view (log : Log) (t : Id) : coreBase.view log t = Past.view log t := rfl
@[simp] theorem coreBase_names : coreBase.names = coreCommandNames := rfl

/-! ## A layer -/

/-- A layer's rule: its name, the refusal a caller sees when it fails, and its check against the base's view of the
event's stream (`BV`), what the layer's memory reads (`V`), and the event (`Ev`). A guard is a rule whose events are the
base's. -/
structure Layer.Rule (BV V Ev : Type) where
  reason : String
  holds : BV → V → Ev → Bool

/-- A layer on base `B` (the core, by default): its commands and events, what its rules remember, its rules (tried in
order: the first that fails is the answer), its guards (rules over the base's events, tried after the base's own rules:
a layer may tighten what is below it, never loosen it), what it shows the layer above (`Exposed`, from what its memory
reads: by default all of it), and what a read of a stream adds (`readJ`, from the memory's state). Its command names
are none of the base's (`names_ok`, by `decide`). -/
structure Layer (B : Base := coreBase) extends Layer.Commands where
  memory : Memory Ev
  rules : List (Layer.Rule B.View memory.V Ev)
  guards : List (Layer.Rule B.View memory.V B.Ev) := []
  Exposed : Type := memory.V
  expose : memory.V → Exposed := by exact fun v => v
  readJ : memory.St → Fields := fun _ => []
  names_ok : B.names.all (fun n => !(schema.map (·.name)).contains n) = true := by decide

/-- An event of a combined log: the base's (`inl`) or the layer's (`inr`). It is its own type rather than
`B.Ev ⊕ L.Ev` so that `simp` can use the lemmas below on a concrete layer, tower or sum: the base and the layer are
implicit arguments of `inl`/`inr`, which `simp`'s index does not look at, where `Sum.inr`'s arguments are the two event
types, which `simp` reads as `Event`/`ItemEvent` on a concrete layer and the generic lemmas as `B.Ev`/`L.Ev`. A layer
writes `.inl e` and `.inr x` as it would for a `Sum`, and matches on them the same way. -/
inductive Layer.XE {B : Base} {L : Layer B} : Type where
  | inl (e : B.Ev)
  | inr (x : L.Ev)
  deriving DecidableEq

namespace Layer
variable {B : Base} (L : Layer B)

/-! ## The combined log -/

/-- An event of the combined log (the base's or the layer's), a combined log, and a request of the combined service. -/
abbrev XEv := @XE B L
abbrev XLog := List L.XEv
abbrev XReq := B.Req ⊕ LRequest L.Cmd

variable {L}

/-- The base's event of a combined event, if it is one. -/
def baseOf : L.XEv → Option B.Ev
  | .inl e => some e
  | .inr _ => none

/-- The base's events of a combined log, in order: its projection to the level below. -/
def bases : L.XLog → List B.Ev := List.filterMap baseOf

/-- The core's events of a combined log over the core. -/
abbrev cores {L : Layer coreBase} (log : L.XLog) : Log := bases log

/-- The layer's events of a combined log, in order. -/
def exts : L.XLog → List (L.Ev) := List.filterMap fun | .inl _ => none | .inr x => some x

/-! Every lemma below is `@[simp]` and fires on a concrete layer, tower or sum as it is (its `.inl e`/`.inr x` are
`Layer.XE.inl`/`Layer.XE.inr`, whose base and layer `simp`'s index ignores). -/

@[simp] theorem baseOf_inl (e : B.Ev) : baseOf (L := L) (.inl e) = some e := rfl
@[simp] theorem baseOf_inr (x : L.Ev) : baseOf (L := L) (.inr x) = none := rfl
@[simp] theorem bases_nil : bases ([] : L.XLog) = [] := rfl
@[simp] theorem exts_nil : exts ([] : L.XLog) = [] := rfl
@[simp] theorem bases_append (a b : L.XLog) : bases (a ++ b) = bases a ++ bases b := List.filterMap_append ..
@[simp] theorem exts_append (a b : L.XLog) : exts (a ++ b) = exts a ++ exts b := List.filterMap_append ..
@[simp] theorem bases_cons_inl (e : B.Ev) (l : L.XLog) : bases (.inl e :: l) = e :: bases l := rfl
@[simp] theorem bases_cons_inr (x : L.Ev) (l : L.XLog) : bases (.inr x :: l) = bases l := rfl
@[simp] theorem exts_cons_inl (e : B.Ev) (l : L.XLog) : exts (.inl e :: l) = exts l := rfl
@[simp] theorem exts_cons_inr (x : L.Ev) (l : L.XLog) : exts (.inr x :: l) = x :: exts l := rfl


/-- The layer's events of stream `t` in a combined log, in order: what the layer's memory reads. -/
def evs (log : L.XLog) (t : Id) : List (L.Ev) := (exts log).filter (L.evStream · == t)

@[simp] theorem mem_bases {e : B.Ev} {log : L.XLog} : e ∈ bases log ↔ .inl e ∈ log := by
  simp [bases, List.mem_filterMap]; constructor
  · rintro ⟨a, h, ha⟩; cases a <;> simp_all [baseOf]
  · intro h; exact ⟨_, h, rfl⟩
@[simp] theorem mem_exts {x : L.Ev} {log : L.XLog} : x ∈ exts log ↔ .inr x ∈ log := by
  simp [exts, List.mem_filterMap]; constructor
  · rintro ⟨a, h, ha⟩; cases a <;> simp_all
  · intro h; exact ⟨_, h, rfl⟩

@[simp] theorem evs_nil (t : Id) : evs ([] : L.XLog) t = [] := rfl
@[simp] theorem evs_append (a b : L.XLog) (t : Id) : evs (a ++ b) t = evs a t ++ evs b t := by
  simp [evs, List.filter_append]
@[simp] theorem evs_cons_inl (e : B.Ev) (l : L.XLog) (t : Id) : evs (.inl e :: l) t = evs l t := rfl
@[simp] theorem evs_cons_inr (x : L.Ev) (l : L.XLog) (t : Id) :
    evs (.inr x :: l) t = if L.evStream x = t then x :: evs l t else evs l t := by
  by_cases h : L.evStream x = t <;> simp only [evs, exts_cons_inr, List.filter_cons, h, beq_self_eq_true] <;> simp [h]
/-- One event, either side, by a `match` on it (for `rw` on an event that is not yet `.inl`/`.inr`). -/
theorem bases_cons (a : L.XEv) (l : L.XLog) :
    bases (a :: l) = (match a with | .inl e => [e] | .inr _ => []) ++ bases l := by cases a <;> rfl
theorem exts_cons (a : L.XEv) (l : L.XLog) :
    exts (a :: l) = (match a with | .inl _ => [] | .inr x => [x]) ++ exts l := by cases a <;> rfl
theorem evs_cons (a : L.XEv) (l : L.XLog) (t : Id) :
    evs (a :: l) t = (match a with | .inl _ => [] | .inr x => if L.evStream x = t then [x] else []) ++ evs l t := by
  cases a with
  | inl e => rfl
  | inr x => by_cases h : L.evStream x = t <;> simp [h]
theorem evs_snoc_inl (l : L.XLog) (e : B.Ev) (t : Id) : evs (l ++ [.inl e]) t = evs l t := by simp
theorem evs_snoc_inr (l : L.XLog) (x : L.Ev) (t : Id) :
    evs (l ++ [.inr x]) t = if L.evStream x = t then evs l t ++ [x] else evs l t := by
  by_cases h : L.evStream x = t <;> simp [h]
/-- The layer events of stream `t` are the log's layer events on `t`. -/
@[simp] theorem mem_evs {x : L.Ev} {log : L.XLog} {t : Id} : x ∈ evs log t ↔ .inr x ∈ log ∧ L.evStream x = t := by
  simp only [evs, List.mem_filter, mem_exts, beq_iff_eq]

/-- The stream of a combined event. -/
def streamX : L.XEv → Id
  | .inl e => B.stream e
  | .inr x => L.evStream x

@[simp] theorem streamX_inl (e : B.Ev) : streamX (L := L) (.inl e) = B.stream e := rfl
@[simp] theorem streamX_inr (x : L.Ev) : streamX (L := L) (.inr x) = L.evStream x := rfl

/-! ## The rules and the guards, combined -/

/-- The first layer rule that `x` fails. -/
def rejectionL (v : B.View) (w : L.memory.V) (x : L.Ev) : Option String :=
  (L.rules.find? (!·.holds v w x)).map (·.reason)

/-- The first guard that the base's event `e` fails. -/
def rejectionG (v : B.View) (w : L.memory.V) (e : B.Ev) : Option String :=
  (L.guards.find? (!·.holds v w e)).map (·.reason)

theorem rejectionL_none {v : B.View} {w : L.memory.V} {x : L.Ev} :
    L.rejectionL v w x = none ↔ ∀ r ∈ L.rules, r.holds v w x = true := by
  simp [rejectionL, List.find?_eq_none]

theorem rejectionG_none {v : B.View} {w : L.memory.V} {e : B.Ev} :
    L.rejectionG v w e = none ↔ ∀ g ∈ L.guards, g.holds v w e = true := by
  simp [rejectionG, List.find?_eq_none]

/-- The first rule a candidate fails against the combined log: for the base's event, the base's rules against the base's
events and then the layer's guards; for the layer's, the layer's rules; each guard and rule against the base's view of
the stream and the memory of the stream's layer events. -/
def rejectionX (log : L.XLog) : L.XEv → Option String
  | .inl e => (B.rejection (bases log) e).or
      (L.rejectionG (B.view (bases log) (B.stream e)) (L.memory.read (evs log (B.stream e))) e)
  | .inr x => L.rejectionL (B.view (bases log) (L.evStream x)) (L.memory.read (evs log (L.evStream x))) x

theorem bases_filter (log : L.XLog) (s : Id) : bases (log.filter (streamX · == s)) = (bases log).filter (B.stream · == s) := by
  induction log with
  | nil => rfl
  | cons e es ih => cases e <;> simp only [List.filter_cons] at ih ⊢ <;> split <;> simp_all [streamX]

theorem exts_filter (log : L.XLog) (s : Id) : exts (log.filter (streamX · == s)) = (exts log).filter (L.evStream · == s) := by
  induction log with
  | nil => rfl
  | cons e es ih => cases e <;> simp only [List.filter_cons] at ih ⊢ <;> split <;> simp_all [streamX]

theorem evs_filter (log : L.XLog) (s : Id) : evs (log.filter (streamX · == s)) s = evs log s := by
  simp only [evs, exts_filter, List.filter_filter, Bool.and_self]

theorem rejectionX_local (log : L.XLog) (e : L.XEv) :
    rejectionX (log.filter (streamX · == streamX e)) e = rejectionX log e := by
  cases e with
  | inl e =>
    rw [show streamX (L := L) (.inl e) = B.stream e from rfl]
    simp only [rejectionX]; rw [bases_filter, evs_filter, B.view_local, B.rejection_local]
  | inr x =>
    rw [show streamX (L := L) (.inr x) = L.evStream x from rfl]
    simp only [rejectionX]; rw [bases_filter, evs_filter, B.view_local]

/-! ## Commands, combined: a layer command mints nothing, so it takes no fresh ids -/

def toEventX : L.XReq → Except String L.XEv
  | .inl r => (B.toEvent r).map .inl
  | .inr (c, cmd, []) => .ok (.inr (L.ofRequest (c, cmd)))
  | .inr _ => .error "fresh_ids"

def toRequestX : L.XEv → L.XReq
  | .inl e => .inl (B.toRequest e)
  | .inr x => .inr ((L.toRequest x).1, (L.toRequest x).2, [])

def reqStreamX : L.XReq → Id
  | .inl r => B.reqStream r
  | .inr (_, cmd, _) => L.stream cmd

theorem toEventX_ok_iff {r : L.XReq} {e : L.XEv} : toEventX r = .ok e ↔ toRequestX e = r := by
  rcases r with r | ⟨c, cmd, _ | ⟨_, _⟩⟩ <;> rcases e with e | x <;>
    simp [toEventX, toRequestX, Service.except_map_ok, B.toEvent_ok_iff]
  constructor
  · rintro rfl; simp [L.toRequest_ofRequest]
  · intro h; rw [← L.ofRequest_toRequest x, show L.toRequest x = (c, cmd) from Prod.ext h.1 h.2]

theorem toEventX_stream {r : L.XReq} {e : L.XEv} (h : toEventX r = .ok e) : streamX e = reqStreamX r := by
  have := toEventX_ok_iff.mp h; subst this
  cases e with
  | inl e => exact B.toEvent_stream (B.toEvent_ok_iff.mpr rfl)
  | inr x => rfl

/-! ## The fast path, combined: the base's state and the layer memory's, side by side -/

def stepX (st : B.St × L.memory.St) : L.XEv → B.St × L.memory.St
  | .inl e => (B.step st.1 e, st.2)
  | .inr x => (st.1, if L.evStream x = B.stStream st.1 then L.memory.step st.2 x else st.2)

def rejectionXS (st : B.St × L.memory.St) : L.XEv → Option String
  | .inl e => (B.rejectionS st.1 e).or (L.rejectionG (B.viewS st.1) (L.memory.view st.2) e)
  | .inr x => L.rejectionL (B.viewS st.1) (L.memory.view st.2) x

theorem foldl_stStream (log : List B.Ev) (st : B.St) : B.stStream (log.foldl B.step st) = B.stStream st := by
  induction log generalizing st with
  | nil => rfl
  | cons e es ih => simp [ih, B.stStream_step]

theorem foldl_stepX (log : L.XLog) (st : B.St × L.memory.St) :
    log.foldl stepX st = ((bases log).foldl B.step st.1,
      ((exts log).filter (L.evStream · == B.stStream st.1)).foldl L.memory.step st.2) := by
  induction log generalizing st with
  | nil => rfl
  | cons e es ih =>
    cases e <;> simp only [List.foldl_cons, ih, stepX, B.stStream_step, bases_cons_inl, bases_cons_inr,
      exts_cons_inl, exts_cons_inr, List.filter_cons] <;> (try split) <;> simp_all

theorem fold_stepX (s : Id) (log : L.XLog) :
    log.foldl stepX (B.init s, L.memory.init) = (B.fold s (bases log), (evs log s).foldl L.memory.step L.memory.init) := by
  rw [foldl_stepX]; simp only [B.stStream_init]; rfl

theorem rejectionXS_fold (log : L.XLog) (e : L.XEv) :
    rejectionXS (log.foldl stepX (B.init (streamX e), L.memory.init)) e = rejectionX log e := by
  rw [fold_stepX]
  cases e with
  | inl e =>
    simp only [rejectionXS, rejectionX, streamX, L.memory.fold_view, Service.fold, B.rejectionS_fold, B.viewS_fold]
  | inr x => simp only [rejectionXS, rejectionX, streamX, L.memory.fold_view, Service.fold, B.viewS_fold]

/-! ## The wire, combined -/

def requestToJL (r : LRequest L.Cmd) : J :=
  .obj [("caller", .obj [("principal", .str r.1)]), ("command", L.cmdToJ r.2.1), ("fresh", .arr (r.2.2.map .str))]

def requestFromJL (j : J) : Except String (LRequest L.Cmd) := do
  let kvs ← fields "request" j
  onlyKeys "request" kvs ["caller", "command", "fresh"]
  let some c := get? kvs "caller" | throw "request.caller: missing"
  let some cmd := get? kvs "command" | throw "request.command: missing"
  let some f := get? kvs "fresh" | throw "request.fresh: missing"
  checked "request" L.requestWf (← callerFromJ c, ← L.cmdFromJ cmd, ← freshFromJ f)

/-- Is this request the layer's: its `command` object names one of the layer's commands. -/
def isLayerRequest (j : J) : Bool :=
  match cmdName j with
  | some n => L.names.contains n
  | none => false

def requestToJX : L.XReq → J
  | .inl r => B.requestToJ r
  | .inr r => requestToJL r

def requestFromJX (j : J) : Except String L.XReq :=
  if isLayerRequest (L := L) j then (requestFromJL j).map .inr else (B.requestFromJ j).map .inl

def requestWfX : L.XReq → Bool
  | .inl r => B.requestWf r
  | .inr r => L.requestWf r

def eventToJX : L.XEv → J
  | .inl e => B.eventToJ e
  | .inr x => L.evToJ x

def eventFromJX (j : J) : Except String L.XEv :=
  if hasName "event" L.names j then (L.evFromJ j).map .inr else (B.eventFromJ j).map .inl

def eventWfX : L.XEv → Bool
  | .inl e => B.eventWf e
  | .inr x => L.evWf x

/-- A snapshot: the base's state (under `core`, so a layer on the core keeps its snapshots' form) and the layer
memory's. Over a layer, the base's state is itself such an object: snapshots nest. -/
def stateToJX (st : B.St × L.memory.St) : J :=
  .obj [("core", B.stateToJ st.1), ("layer", L.memory.stateToJ st.2)]

def stateFromJX (j : J) : Except String (B.St × L.memory.St) := do
  let kvs ← fields "state" j
  let some c := get? kvs "core" | throw "state.core: missing"
  let some x := get? kvs "layer" | throw "state.layer: missing"
  return (← B.stateFromJ c, ← L.memory.stateFromJ x)

/-- A read of a stream: the base's read, with the layer's fields added when the stream exists. -/
def streamSJX (st : B.St × L.memory.St) : J :=
  match B.streamSJ st.1 with
  | .obj kvs => if B.live st.1 then .obj (kvs ++ L.readJ st.2) else .obj kvs
  | j => j

theorem names_disjoint {n : String} (hn : n ∈ B.names) : L.names.contains n = false := by
  have := List.all_eq_true.mp L.names_ok n hn
  simpa [Commands.names] using this

theorem requestFromJX_toJ (r : L.XReq) (h : requestWfX r = true) : requestFromJX (requestToJX r) = .ok r := by
  rcases r with r | ⟨c, cmd, f⟩
  · obtain ⟨n, hn, hm⟩ := B.requestToJ_name r
    have : isLayerRequest (L := L) (B.requestToJ r) = false := by
      simp only [isLayerRequest, hn, names_disjoint hm]
    simp only [requestFromJX, requestToJX, this, Bool.false_eq_true, ite_false]
    rw [B.requestFromJ_toJ r h]; rfl
  · have hcmd : L.cmdWf cmd = true := by simp_all [requestWfX, Commands.requestWf]
    have hl : isLayerRequest (L := L) (requestToJL (c, cmd, f)) = true := by
      simpa [isLayerRequest, requestToJL, cmdName, get?, List.find?, Commands.cmdToJ, keyStr_objToJ] using
        Commands.toVals_mem cmd
    have hr := checked_ok (w := "request") (show L.requestWf (c, cmd, f) = true from h)
    simp only [requestFromJX, requestToJX, hl, ite_true]
    simp_all [requestFromJL, requestToJL, fields, onlyKeys, get?, List.find?, callerFromJ, str,
      Commands.cmdFromJ_toJ cmd hcmd, freshFromJ, strs_toJ, bind, Except.bind, Except.map]

theorem requestFromJX_wf {j : J} {r : L.XReq} (h : requestFromJX j = .ok r) : requestWfX r = true := by
  unfold requestFromJX at h
  split at h <;> obtain ⟨a, ha, rfl⟩ := Service.except_map_ok.mp h
  · unfold requestFromJL at ha
    simp only [bind, Except.bind] at ha
    repeat (first | (split at ha <;> try contradiction) | exact (checked_wf ha :))
  · exact B.requestFromJ_wf ha

theorem eventFromJX_toJ (e : L.XEv) (h : eventWfX e = true) : eventFromJX (eventToJX e) = .ok e := by
  cases e with
  | inl e =>
    obtain ⟨n, hn, hm⟩ := B.eventToJ_name e
    have : hasName "event" L.names (B.eventToJ e) = false := by simp only [hasName, hn, names_disjoint hm]
    simp only [eventFromJX, eventToJX, this, Bool.false_eq_true, ite_false]
    rw [B.eventFromJ_toJ e h]; rfl
  | inr x =>
    have : hasName "event" L.names (L.evToJ x) = true := by
      simpa [hasName, Commands.evToJ, keyStr_objToJ] using Commands.toVals_mem (L.toRequest x).2
    simp only [eventFromJX, eventToJX, this, ite_true]
    rw [Commands.evFromJ_toJ x h]; rfl

theorem eventFromJX_wf {j : J} {e : L.XEv} (h : eventFromJX j = .ok e) : eventWfX e = true := by
  unfold eventFromJX at h
  split at h <;> obtain ⟨a, ha, rfl⟩ := Service.except_map_ok.mp h
  · exact Commands.evFromJ_wf ha
  · exact B.eventFromJ_wf ha

theorem stateFromJX_toJ (st : B.St × L.memory.St) : stateFromJX (stateToJX st) = .ok st := by
  obtain ⟨c, x⟩ := st
  simp [stateFromJX, stateToJX, fields, get?, List.find?, B.stateFromJ_toJ, L.memory.stateFromJ_toJ, bind,
    Except.bind, pure, Except.pure]

/-! ## The combined service -/

/-- The base and the layer, as one service: the engine serves it, and `Service.lean` proves it. -/
abbrev service (L : Layer B) : Service where
  Ev := L.XEv
  Req := L.XReq
  St := B.St × L.memory.St
  toEvent := toEventX
  toRequest := toRequestX
  toEvent_ok_iff := toEventX_ok_iff
  stream := streamX
  reqStream := reqStreamX
  toEvent_stream := toEventX_stream
  ok log e := (rejectionX log e).isNone
  rejection := rejectionX
  rejection_none_iff _ _ := by simp [Option.isNone_iff_eq_none]
  rejection_local := rejectionX_local
  init s := (B.init s, L.memory.init)
  step := stepX
  rejectionS := rejectionXS
  rejectionS_fold := rejectionXS_fold
  stStream st := B.stStream st.1
  stStream_init s := B.stStream_init s
  stStream_step st e := by cases e <;> simp [stepX, B.stStream_step]
  requestWf := requestWfX
  eventWf := eventWfX
  eventWf_eq e := by cases e <;> simp [eventWfX, requestWfX, toRequestX, B.eventWf_eq, Commands.evWf]
  requestToJ := requestToJX
  requestFromJ := requestFromJX
  requestFromJ_toJ := requestFromJX_toJ
  requestFromJ_wf := requestFromJX_wf
  eventToJ := eventToJX
  eventFromJ := eventFromJX
  eventFromJ_toJ := eventFromJX_toJ
  eventFromJ_wf := eventFromJX_wf
  stateToJ := stateToJX
  stateFromJ := stateFromJX
  stateFromJ_toJ := stateFromJX_toJ
  streamSJ := streamSJX

/-! ## A layer is a base: towers -/

/-- **A layer, with everything below it, is a base** for the layer above: its service is `L.service`, its view of a
stream is the base's view and what the layer exposes of its memory (`Exposed`), and its names are the base's and the
layer's. A layer on `L.toBase` reads both, adds its own commands and events, and may guard any of `L.service`'s. -/
abbrev toBase (L : Layer B) : Base where
  toService := L.service
  View := B.View × L.Exposed
  view log t := (B.view (bases log) t, L.expose (L.memory.read (evs log t)))
  view_local log s := by
    show (B.view (bases (log.filter (streamX · == s))) s, L.expose (L.memory.read (evs (log.filter (streamX · == s)) s))) = _
    rw [bases_filter, evs_filter, B.view_local]
  viewS st := (B.viewS st.1, L.expose (L.memory.view st.2))
  viewS_fold s log := by
    show (B.viewS (log.foldl stepX (B.init s, L.memory.init)).1, L.expose (L.memory.view (log.foldl stepX (B.init s, L.memory.init)).2)) = _
    rw [fold_stepX]; simp only [Service.fold, B.viewS_fold, L.memory.fold_view]
  live st := B.live st.1
  names := B.names ++ L.names
  requestToJ_name r := by
    rcases r with r | ⟨c, cmd, f⟩
    · obtain ⟨n, h1, h2⟩ := B.requestToJ_name r
      exact ⟨n, h1, List.mem_append_left _ h2⟩
    · refine ⟨(L.toVals cmd).1, ?_, List.mem_append_right _ ?_⟩
      · simp [requestToJX, requestToJL, cmdName, get?, List.find?, Commands.cmdToJ, keyStr_objToJ]
      · simpa using Commands.toVals_mem cmd
  eventToJ_name e := by
    rcases e with e | x
    · obtain ⟨n, h1, h2⟩ := B.eventToJ_name e
      exact ⟨n, h1, List.mem_append_left _ h2⟩
    · refine ⟨(L.toVals (L.toRequest x).2).1, ?_, List.mem_append_right _ ?_⟩
      · simp [eventToJX, Commands.evToJ, keyStr_objToJ]
      · simpa using Commands.toVals_mem (L.toRequest x).2

/-- What `L.toBase` shows the layer above of a stream: the base's view, and what `L` exposes of its memory. -/
@[simp] theorem toBase_view (L : Layer B) (log : L.XLog) (t : Id) :
    L.toBase.view log t = (B.view (bases log) t, L.expose (L.memory.read (evs log t))) := rfl
@[simp] theorem toBase_names (L : Layer B) : L.toBase.names = B.names ++ L.names := rfl
/-- `L.toBase`'s service, events and valid logs are `L`'s. -/
theorem toBase_service (L : Layer B) : L.toBase.toService = L.service := rfl

/-! ## Every layer keeps its base's guarantees, its own rules and its guards -/

/-- A combined log built only by accepting candidates (`Service.Valid` at `L.service`). -/
abbrev ValidX : L.XLog → Prop := L.service.Valid

/-- **The base's log inside a valid combined log is valid at the base.** So every theorem proved of a valid log of the
base holds of the base's events of a valid combined log: a layer cannot break what is below it. Over a tower it
applies at each level (`h.base.base`). -/
theorem ValidX.base {log : L.XLog} (h : ValidX log) : B.Valid (bases log) := by
  refine Service.Valid.project (S := L.service) baseOf (fun log e _ hok e' he => ?_) h
  cases e with
  | inr x => cases he
  | inl e =>
    simp only [baseOf, Option.some.injEq] at he; subst he
    have hn : rejectionX log (.inl e) = none := Option.isNone_iff_eq_none.mp hok
    simp only [rejectionX, Option.or_eq_none_iff] at hn
    exact (B.rejection_none_iff _ _).mp hn.1

/-- **The core's events of a valid combined log over the core form a `Valid` core log** (`ValidX.base` at the core). -/
theorem ValidX.cores {L : Layer coreBase} {log : L.XLog} (h : ValidX log) : Valid (cores log) := h.base

/-- **No layer can change a stream's proof revision**: in a valid combined log over the core, every creation of a stream
carries the revision of the core's events (`proof_revision_unique` through `ValidX.cores`). A layer's own events are
not core events and carry no revision; over a tower, the same holds one level down per `.base`. -/
theorem ValidX.proof_revision_unique {L : Layer coreBase} {log : L.XLog} (h : ValidX log) {a t : Id} {u : Creation}
    {m : Meta} (hc : .inl (Event.streamCreate a t u m) ∈ log) : proofRevision (Layer.cores log) t = some u.url :=
  StreamCore.proof_revision_unique h.cores (mem_bases.mpr hc)

/-- Once the core's events of a combined log give a stream a revision, appending anything, the layer's events or the
core's, keeps it (`proof_revision_fixed`). No hypothesis. -/
theorem proof_revision_fixedX {L : Layer coreBase} {log : L.XLog} {t : Id} {u : String}
    (h : proofRevision (cores log) t = some u) (post : L.XLog) : proofRevision (cores (log ++ post)) t = some u := by
  simpa [cores] using StreamCore.proof_revision_fixed h (bases post)

/-- **A layer event of a valid combined log held every layer rule** against the base's view of its stream and the
memory of the stream's layer events before it. A layer proves its own theorems from this. -/
theorem ValidX.holds {pre post : L.XLog} {x : L.Ev} (h : ValidX (pre ++ .inr x :: post))
    {r : Layer.Rule B.View L.memory.V L.Ev} (hr : r ∈ L.rules) :
    r.holds (B.view (bases pre) (L.evStream x)) (L.memory.read (evs pre (L.evStream x))) x = true := by
  have := Service.Valid.okAt h
  exact rejectionL_none.mp (Option.isNone_iff_eq_none.mp this) r hr

/-- **The rule named `n` held for a layer event of a valid combined log**, by its name rather than its position:
`h.holdsNamed "unknown_note"` is that rule's `holds … = true` (the rule is found by `rfl`, so inserting or reordering
rules does not change the proof). -/
theorem ValidX.holdsNamed {pre post : L.XLog} {x : L.Ev} (h : ValidX (pre ++ .inr x :: post)) (n : String)
    {r : Layer.Rule B.View L.memory.V L.Ev} (hr : L.rules.find? (·.reason == n) = some r := by rfl) :
    r.holds (B.view (bases pre) (L.evStream x)) (L.memory.read (evs pre (L.evStream x))) x = true :=
  h.holds (List.mem_of_find?_eq_some hr)

/-- **A base event of a valid combined log held every guard** of the layer, against the base's view of its stream and
the memory of the stream's layer events before it. -/
theorem ValidX.guardHolds {pre post : L.XLog} {e : B.Ev} (h : ValidX (pre ++ .inl e :: post))
    {g : Layer.Rule B.View L.memory.V B.Ev} (hg : g ∈ L.guards) :
    g.holds (B.view (bases pre) (B.stream e)) (L.memory.read (evs pre (B.stream e))) e = true := by
  have : (rejectionX pre (.inl e)).isNone = true := Service.Valid.okAt h
  have := (Option.or_eq_none_iff.mp (Option.isNone_iff_eq_none.mp this)).2
  exact rejectionG_none.mp this g hg

/-- **The guard named `n` held for a base event of a valid combined log**, by its name (found by `rfl`). -/
theorem ValidX.guardHoldsNamed {pre post : L.XLog} {e : B.Ev} (h : ValidX (pre ++ .inl e :: post)) (n : String)
    {g : Layer.Rule B.View L.memory.V B.Ev} (hg : L.guards.find? (·.reason == n) = some g := by rfl) :
    g.holds (B.view (bases pre) (B.stream e)) (L.memory.read (evs pre (B.stream e))) e = true :=
  h.guardHolds (List.mem_of_find?_eq_some hg)

/-- **A layer event is accepted after a valid log iff every layer rule holds for it**, against the base's view of its
stream and the memory of the stream's layer events before it: the converse of `ValidX.holds`, so "X is accepted when
..." is a theorem about valid logs. -/
theorem ValidX.snoc_inr_iff {pre : L.XLog} (h : ValidX pre) {x : L.Ev} :
    ValidX (pre ++ [.inr x]) ↔
      ∀ r ∈ L.rules, r.holds (B.view (bases pre) (L.evStream x)) (L.memory.read (evs pre (L.evStream x))) x = true := by
  constructor
  · intro hv r hr; exact ValidX.holds (post := []) hv hr
  · intro hr
    exact Service.Valid.snoc h (Option.isNone_iff_eq_none.mpr (rejectionL_none.mpr hr))

/-- **A base event is accepted after a valid log iff the base accepts it and every guard holds for it**: the converse
of `ValidX.base` and `ValidX.guardHolds` for one event. -/
theorem ValidX.snoc_inl_iff {pre : L.XLog} (h : ValidX pre) {e : B.Ev} :
    ValidX (pre ++ [.inl e]) ↔ B.rejection (bases pre) e = none ∧
      ∀ g ∈ L.guards, g.holds (B.view (bases pre) (B.stream e)) (L.memory.read (evs pre (B.stream e))) e = true := by
  constructor
  · intro hv
    have : (rejectionX pre (.inl e)).isNone = true := Service.Valid.okAt (post := []) hv
    have := Option.or_eq_none_iff.mp (Option.isNone_iff_eq_none.mp this)
    exact ⟨this.1, rejectionG_none.mp this.2⟩
  · rintro ⟨hb, hg⟩
    refine Service.Valid.snoc h (Option.isNone_iff_eq_none.mpr ?_)
    exact Option.or_eq_none_iff.mpr ⟨hb, rejectionG_none.mpr hg⟩

end Layer

/-- `ValidX.base` from `L.service.Valid`: what `h.base` is when `h` is itself a base's validity, one level up, so
`h.base.base` goes down two levels of a tower. -/
theorem Service.Valid.base {B : Base} {L : Layer B} {log : L.XLog} (h : L.service.Valid log) :
    B.Valid (Layer.bases log) := Layer.ValidX.base h

/-! ## Independent layers side by side: the sum -/

/-- An event of two layers side by side: the first's (`inl`) or the second's (`inr`); its own type rather than a `Sum`,
as `Layer.XE`, so that `simp` uses the sum's lemmas on a concrete sum. -/
inductive Layer.Commands.SE {C₁ C₂ : Layer.Commands} : Type where
  | inl (x : C₁.Ev)
  | inr (x : C₂.Ev)
  deriving DecidableEq

namespace Layer.Commands

/-- The first side's event of a sum's event, if it is one. -/
def SE.left? {C₁ C₂ : Layer.Commands} : @SE C₁ C₂ → Option C₁.Ev
  | .inl x => some x
  | .inr _ => none

/-- The second side's event of a sum's event, if it is one. -/
def SE.right? {C₁ C₂ : Layer.Commands} : @SE C₁ C₂ → Option C₂.Ev
  | .inl _ => none
  | .inr x => some x

@[simp] theorem SE.left?_inl {C₁ C₂ : Layer.Commands} (x : C₁.Ev) : (SE.inl (C₂ := C₂) x).left? = some x := rfl
@[simp] theorem SE.left?_inr {C₁ C₂ : Layer.Commands} (x : C₂.Ev) : (SE.inr (C₁ := C₁) x).left? = none := rfl
@[simp] theorem SE.right?_inl {C₁ C₂ : Layer.Commands} (x : C₁.Ev) : (SE.inl (C₂ := C₂) x).right? = none := rfl
@[simp] theorem SE.right?_inr {C₁ C₂ : Layer.Commands} (x : C₂.Ev) : (SE.inr (C₁ := C₁) x).right? = some x := rfl
@[simp] theorem filterMap_left?_inl {C₁ C₂ : Layer.Commands} (x : C₁.Ev) (l : List (@SE C₁ C₂)) :
    (.inl x :: l).filterMap SE.left? = x :: l.filterMap SE.left? := rfl
@[simp] theorem filterMap_left?_inr {C₁ C₂ : Layer.Commands} (x : C₂.Ev) (l : List (@SE C₁ C₂)) :
    (.inr x :: l).filterMap SE.left? = l.filterMap SE.left? := rfl
@[simp] theorem filterMap_right?_inl {C₁ C₂ : Layer.Commands} (x : C₁.Ev) (l : List (@SE C₁ C₂)) :
    (.inl x :: l).filterMap SE.right? = l.filterMap SE.right? := rfl
@[simp] theorem filterMap_right?_inr {C₁ C₂ : Layer.Commands} (x : C₂.Ev) (l : List (@SE C₁ C₂)) :
    (.inr x :: l).filterMap SE.right? = x :: l.filterMap SE.right? := rfl

/-- Two layers' commands and events side by side, their names disjoint: each command and event is on the wire as it is
alone (its schema's entry is found under its name in the concatenated schema). -/
abbrev sum (C₁ C₂ : Layer.Commands) (h : (C₁.names.all fun n => !C₂.names.contains n) = true) : Layer.Commands where
  Cmd := C₁.Cmd ⊕ C₂.Cmd
  Ev := @SE C₁ C₂
  toRequest
    | .inl e => ((C₁.toRequest e).1, .inl (C₁.toRequest e).2)
    | .inr e => ((C₂.toRequest e).1, .inr (C₂.toRequest e).2)
  ofRequest
    | (a, .inl c) => .inl (C₁.ofRequest (a, c))
    | (a, .inr c) => .inr (C₂.ofRequest (a, c))
  stream
    | .inl c => C₁.stream c
    | .inr c => C₂.stream c
  schema := C₁.schema ++ C₂.schema
  toVals
    | .inl c => C₁.toVals c
    | .inr c => C₂.toVals c
  ofVals n vs := if C₁.names.contains n then (C₁.ofVals n vs).map .inl else (C₂.ofVals n vs).map .inr
  ofRequest_toRequest e := by cases e <;> simp [C₁.ofRequest_toRequest, C₂.ofRequest_toRequest]
  toRequest_ofRequest r := by
    obtain ⟨a, c | c⟩ := r <;> simp [C₁.toRequest_ofRequest, C₂.toRequest_ofRequest]
  ofVals_toVals c := by
    cases c with
    | inl c =>
      have hm : (C₁.toVals c).1 ∈ C₁.names := by simpa using C₁.toVals_mem c
      simp [hm, C₁.ofVals_toVals]
    | inr c =>
      have h2 : (C₂.toVals c).1 ∈ C₂.names := by simpa using C₂.toVals_mem c
      have h1 : (C₂.toVals c).1 ∉ C₁.names := fun hm => by
        have := List.all_eq_true.mp h _ hm; simp_all
      simp [h1, C₂.ofVals_toVals]
  schema_ok := by
    have h1 := C₁.schema_ok; have h2 := C₂.schema_ok
    simp only [schemaOk, Bool.and_eq_true, List.all_eq_true, List.map_append, List.contains_append,
      Bool.not_eq_true', Bool.or_eq_false_iff, List.mem_append] at h1 h2 ⊢
    exact ⟨fun n hn => ⟨h1.1 n hn, h2.1 n hn⟩, fun sc hsc => hsc.elim (h1.2 sc) (h2.2 sc)⟩
  toVals_name c := by
    cases c with
    | inl c => simp [(by simpa [names] using C₁.toVals_mem c : _)]
    | inr c => simp [(by simpa [names] using C₂.toVals_mem c : _)]

end Layer.Commands

/-- Two memories side by side: each reads its own side's events. Its snapshot is `{"left", "right"}`. -/
abbrev Memory.sum {C₁ C₂ : Layer.Commands} (M₁ : Memory C₁.Ev) (M₂ : Memory C₂.Ev) :
    Memory (@Layer.Commands.SE C₁ C₂) where
  V := M₁.V × M₂.V
  read past := (M₁.read (past.filterMap Layer.Commands.SE.left?), M₂.read (past.filterMap Layer.Commands.SE.right?))
  St := M₁.St × M₂.St
  init := (M₁.init, M₂.init)
  step st e := match e with
    | .inl e => (M₁.step st.1 e, st.2)
    | .inr e => (st.1, M₂.step st.2 e)
  view st := (M₁.view st.1, M₂.view st.2)
  fold_view past := by
    suffices ∀ st, past.foldl (fun st e => match e with
        | .inl e => (M₁.step st.1 e, st.2) | .inr e => (st.1, M₂.step st.2 e)) st =
        ((past.filterMap Layer.Commands.SE.left?).foldl M₁.step st.1, (past.filterMap Layer.Commands.SE.right?).foldl M₂.step st.2) by
      rw [this]; simp only [M₁.fold_view, M₂.fold_view]
    induction past with
    | nil => intro; rfl
    | cons e es ih => intro st; cases e <;> simp [ih, List.filterMap_cons, Layer.Commands.SE.left?, Layer.Commands.SE.right?]
  stateToJ st := .obj [("left", M₁.stateToJ st.1), ("right", M₂.stateToJ st.2)]
  stateFromJ j := do
    let kvs ← fields "state" j
    let some a := get? kvs "left" | throw "state.left: missing"
    let some b := get? kvs "right" | throw "state.right: missing"
    return (← M₁.stateFromJ a, ← M₂.stateFromJ b)
  stateFromJ_toJ st := by
    obtain ⟨a, b⟩ := st
    simp [fields, get?, List.find?, M₁.stateFromJ_toJ, M₂.stateFromJ_toJ, bind, Except.bind, pure, Except.pure]

namespace Layer
variable {B : Base}

/-- A rule of one side, as a rule of the sum: it reads its side's memory and holds for the other side's events. -/
def Rule.left {BV V₁ V₂ : Type} {C₁ C₂ : Commands} (r : Layer.Rule BV V₁ C₁.Ev) :
    Layer.Rule BV (V₁ × V₂) (@Commands.SE C₁ C₂) :=
  ⟨r.reason, fun v w e => match e with | .inl x => r.holds v w.1 x | .inr _ => true⟩
def Rule.right {BV V₁ V₂ : Type} {C₁ C₂ : Commands} (r : Layer.Rule BV V₂ C₂.Ev) :
    Layer.Rule BV (V₁ × V₂) (@Commands.SE C₁ C₂) :=
  ⟨r.reason, fun v w e => match e with | .inl _ => true | .inr x => r.holds v w.2 x⟩
/-- A guard of one side, as a guard of the sum: it reads its side's memory. -/
def Rule.guardLeft {BV V₁ V₂ E : Type} (g : Layer.Rule BV V₁ E) : Layer.Rule BV (V₁ × V₂) E :=
  ⟨g.reason, fun v w e => g.holds v w.1 e⟩
def Rule.guardRight {BV V₁ V₂ E : Type} (g : Layer.Rule BV V₂ E) : Layer.Rule BV (V₁ × V₂) E :=
  ⟨g.reason, fun v w e => g.holds v w.2 e⟩

/-- **Two independent layers on the same base, side by side**: the events of either, the memories side by side (each
side's rules read its own), the rules of both (each holds for the other side's events), the guards of both, what both
expose, the reads of both. Their names are disjoint (`h`, by `decide`), and each is disjoint from the base's. -/
abbrev sum (L₁ L₂ : Layer B) (h : (L₁.names.all fun n => !L₂.names.contains n) = true := by decide) : Layer B where
  toCommands := L₁.toCommands.sum L₂.toCommands h
  memory := Memory.sum (C₁ := L₁.toCommands) (C₂ := L₂.toCommands) L₁.memory L₂.memory
  rules := L₁.rules.map Rule.left ++ L₂.rules.map Rule.right
  guards := L₁.guards.map Rule.guardLeft ++ L₂.guards.map Rule.guardRight
  Exposed := L₁.Exposed × L₂.Exposed
  expose w := (L₁.expose w.1, L₂.expose w.2)
  readJ st := L₁.readJ st.1 ++ L₂.readJ st.2
  names_ok := by
    apply List.all_eq_true.mpr; intro n hn
    have a := List.all_eq_true.mp L₁.names_ok n hn; have b := List.all_eq_true.mp L₂.names_ok n hn
    simp_all

section
variable {L₁ L₂ : Layer B} {h : (L₁.names.all fun n => !L₂.names.contains n) = true}

/-- A sum's event, as the left side's (the base's events kept, the right side's dropped). -/
def projL : (L₁.sum L₂ h).XEv → Option L₁.XEv
  | .inl e => some (.inl e)
  | .inr (.inl x) => some (.inr x)
  | .inr (.inr _) => none

/-- A sum's event, as the right side's. -/
def projR : (L₁.sum L₂ h).XEv → Option L₂.XEv
  | .inl e => some (.inl e)
  | .inr (.inl _) => none
  | .inr (.inr x) => some (.inr x)

@[simp] theorem projL_inl (e : B.Ev) : projL (h := h) (.inl e) = some (.inl e) := rfl
@[simp] theorem projL_inr_inl (x : L₁.Ev) : projL (h := h) (.inr (.inl x)) = some (.inr x) := rfl
@[simp] theorem projL_inr_inr (x : L₂.Ev) : projL (h := h) (.inr (.inr x)) = none := rfl
@[simp] theorem projR_inl (e : B.Ev) : projR (h := h) (.inl e) = some (.inl e) := rfl
@[simp] theorem projR_inr_inl (x : L₁.Ev) : projR (h := h) (.inr (.inl x)) = none := rfl
@[simp] theorem projR_inr_inr (x : L₂.Ev) : projR (h := h) (.inr (.inr x)) = some (.inr x) := rfl

/-! A side of a sum's log, one event at a time (`simp` cannot use `List.filterMap_cons_none` itself). -/
@[simp] theorem filterMap_projL_inl (e : B.Ev) (l : (L₁.sum L₂ h).XLog) :
    (.inl e :: l).filterMap projL = .inl e :: l.filterMap projL := rfl
@[simp] theorem filterMap_projL_inr_inl (x : L₁.Ev) (l : (L₁.sum L₂ h).XLog) :
    (.inr (.inl x) :: l).filterMap projL = .inr x :: l.filterMap projL := rfl
@[simp] theorem filterMap_projL_inr_inr (x : L₂.Ev) (l : (L₁.sum L₂ h).XLog) :
    (.inr (.inr x) :: l).filterMap projL = l.filterMap projL := rfl
@[simp] theorem filterMap_projR_inl (e : B.Ev) (l : (L₁.sum L₂ h).XLog) :
    (.inl e :: l).filterMap projR = .inl e :: l.filterMap projR := rfl
@[simp] theorem filterMap_projR_inr_inl (x : L₁.Ev) (l : (L₁.sum L₂ h).XLog) :
    (.inr (.inl x) :: l).filterMap projR = l.filterMap projR := rfl
@[simp] theorem filterMap_projR_inr_inr (x : L₂.Ev) (l : (L₁.sum L₂ h).XLog) :
    (.inr (.inr x) :: l).filterMap projR = .inr x :: l.filterMap projR := rfl

theorem bases_projL (log : (L₁.sum L₂ h).XLog) : bases (log.filterMap projL) = bases log := by
  induction log with
  | nil => rfl
  | cons e es ih => rcases e with e | x | x <;> simp_all [projL, List.filterMap_cons]

theorem bases_projR (log : (L₁.sum L₂ h).XLog) : bases (log.filterMap projR) = bases log := by
  induction log with
  | nil => rfl
  | cons e es ih => rcases e with e | x | x <;> simp_all [projR, List.filterMap_cons]

theorem exts_projL (log : (L₁.sum L₂ h).XLog) : exts (log.filterMap projL) = (exts log).filterMap Commands.SE.left? := by
  induction log with
  | nil => rfl
  | cons e es ih => rcases e with e | x | x <;> simp_all [projL, List.filterMap_cons, Commands.SE.left?]

theorem exts_projR (log : (L₁.sum L₂ h).XLog) : exts (log.filterMap projR) = (exts log).filterMap Commands.SE.right? := by
  induction log with
  | nil => rfl
  | cons e es ih => rcases e with e | x | x <;> simp_all [projR, List.filterMap_cons, Commands.SE.right?]

theorem evs_projL (log : (L₁.sum L₂ h).XLog) (t : Id) :
    evs (log.filterMap projL) t = (evs log t).filterMap Commands.SE.left? := by
  simp only [evs, exts_projL]
  generalize exts log = l
  induction l with
  | nil => rfl
  | cons e es ih =>
    rcases e with x | x
    · by_cases hs : L₁.evStream x = t <;>
        simp_all [Commands.SE.left?, Commands.evStream]
    · by_cases hs : L₂.evStream x = t <;>
        simp_all [List.filterMap_cons, Commands.SE.left?, Commands.evStream]

theorem evs_projR (log : (L₁.sum L₂ h).XLog) (t : Id) :
    evs (log.filterMap projR) t = (evs log t).filterMap Commands.SE.right? := by
  simp only [evs, exts_projR]
  generalize exts log = l
  induction l with
  | nil => rfl
  | cons e es ih =>
    rcases e with x | x
    · by_cases hs : L₁.evStream x = t <;>
        simp_all [List.filterMap_cons, Commands.SE.right?, Commands.evStream]
    · by_cases hs : L₂.evStream x = t <;>
        simp_all [Commands.SE.right?, Commands.evStream]

/-- **The left side of a valid sum is valid alone**: the base's events and the left layer's, in order, form a valid
log of `L₁` over the base. -/
theorem ValidX.left {log : (L₁.sum L₂ h).XLog} (hv : ValidX log) : ValidX (log.filterMap projL) := by
  refine Service.Valid.project (S := (L₁.sum L₂ h).service) (T := L₁.service) (projL (h := h)) (fun log e _ hok e' he => ?_) hv
  have hok : rejectionX log e = none := Option.isNone_iff_eq_none.mp hok
  show (rejectionX _ e').isNone = true
  rw [Option.isNone_iff_eq_none]
  rcases e with e | x | x <;> simp only [projL, Option.some.injEq, reduceCtorEq] at he <;> subst he
  · simp only [rejectionX, Option.or_eq_none_iff, rejectionG_none] at hok ⊢
    refine ⟨by rw [bases_projL]; exact hok.1, fun g hg => ?_⟩
    have := hok.2 (Rule.guardLeft g) (List.mem_append_left _ (List.mem_map_of_mem hg))
    simpa [Rule.guardLeft, Memory.sum, bases_projL, evs_projL] using this
  · have hok := rejectionL_none.mp hok
    apply rejectionL_none.mpr
    intro r hr
    have := hok (Rule.left r) (List.mem_append_left _ (List.mem_map_of_mem hr))
    simpa [Rule.left, Memory.sum, bases_projL, evs_projL, Commands.evStream, Commands.sum] using this

/-- **The right side of a valid sum is valid alone.** -/
theorem ValidX.right {log : (L₁.sum L₂ h).XLog} (hv : ValidX log) : ValidX (log.filterMap projR) := by
  refine Service.Valid.project (S := (L₁.sum L₂ h).service) (T := L₂.service) (projR (h := h)) (fun log e _ hok e' he => ?_) hv
  have hok : rejectionX log e = none := Option.isNone_iff_eq_none.mp hok
  show (rejectionX _ e').isNone = true
  rw [Option.isNone_iff_eq_none]
  rcases e with e | x | x <;> simp only [projR, Option.some.injEq, reduceCtorEq] at he <;> subst he
  · simp only [rejectionX, Option.or_eq_none_iff, rejectionG_none] at hok ⊢
    refine ⟨by rw [bases_projR]; exact hok.1, fun g hg => ?_⟩
    have := hok.2 (Rule.guardRight g) (List.mem_append_right _ (List.mem_map_of_mem hg))
    simpa [Rule.guardRight, Memory.sum, bases_projR, evs_projR] using this
  · have hok := rejectionL_none.mp hok
    apply rejectionL_none.mpr
    intro r hr
    have := hok (Rule.right r) (List.mem_append_right _ (List.mem_map_of_mem hr))
    simpa [Rule.right, Memory.sum, bases_projR, evs_projR, Commands.evStream, Commands.sum] using this

/-- **A left event of a valid sum held every rule of the left layer**, as it would alone: against the base's view and
the left memory of the left events before it. -/
theorem ValidX.holdsLeft {pre post : (L₁.sum L₂ h).XLog} {x : L₁.Ev} (hv : ValidX (pre ++ .inr (.inl x) :: post))
    {r : Layer.Rule B.View L₁.memory.V L₁.Ev} (hr : r ∈ L₁.rules) :
    r.holds (B.view (bases pre) (L₁.evStream x)) (L₁.memory.read (evs (pre.filterMap projL) (L₁.evStream x))) x = true := by
  have hv' : ValidX (pre.filterMap projL ++ .inr x :: post.filterMap projL) := by
    simpa [List.filterMap_append, projL] using ValidX.left hv
  simpa [bases_projL] using hv'.holds hr

/-- **A right event of a valid sum held every rule of the right layer**, as it would alone. -/
theorem ValidX.holdsRight {pre post : (L₁.sum L₂ h).XLog} {x : L₂.Ev} (hv : ValidX (pre ++ .inr (.inr x) :: post))
    {r : Layer.Rule B.View L₂.memory.V L₂.Ev} (hr : r ∈ L₂.rules) :
    r.holds (B.view (bases pre) (L₂.evStream x)) (L₂.memory.read (evs (pre.filterMap projR) (L₂.evStream x))) x = true := by
  have hv' : ValidX (pre.filterMap projR ++ .inr x :: post.filterMap projR) := by
    simpa [List.filterMap_append, projR] using ValidX.right hv
  simpa [bases_projR] using hv'.holds hr

end
end Layer
end StreamCore
