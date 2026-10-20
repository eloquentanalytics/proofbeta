-- Copyright (c) 2026 the proofbeta authors. All rights reserved. See LICENSE.
import StreamCore.Command

/-!
# The fast path: a stream's state, folded event by event

The engine keeps, per stream, a small state that each accepted event updates (`StreamState.step`); the rules read
their `View` from it (`StreamState.view`) and decide with it (`rejectionS`; `respondS` is the generic answer from it,
`Core.lean`). A snapshot is a state and the number of events it folds.
-/

namespace StreamCore

/-- Add `x` to the end of `l` unless it is there: a list used as a set, in order of first mention. -/
def addU (x : Id) (l : List Id) : List Id := if l.contains x then l else l ++ [x]

theorem mem_addU {x p : Id} {l : List Id} : p ∈ addU x l ↔ p ∈ l ∨ x = p := by
  unfold addU
  split
  · rename_i h
    constructor
    · exact .inl
    · rintro (hp | rfl)
      · exact hp
      · exact List.elem_iff.mp h
  · simp [eq_comm]

theorem beq_eq_decide (a b : Id) : (a == b) = decide (a = b) := by rw [Bool.eq_iff_iff]; simp

/-- One stream's state: what the rules need to know about its past, and what reads show. -/
structure StreamState where
  stream : Id
  created : Bool := false
  creator : Option Id := none
  url : Option String := none
  /-- Every principal that ever joined: the creator, and every principal invited. -/
  joined : List Id := []
  banned : List Id := []
  /-- Every principal whose latest creation, promotion, demotion or ban made it an admin. -/
  admins : List Id := []
  ended : Bool := false
  deriving Repr, DecidableEq

def StreamState.init (s : Id) : StreamState := { stream := s }

/-- The first value given, kept. -/
def keep {α} (o : Option α) (x : α) : Option α :=
  match o with
  | some y => some y
  | none => some x

def StreamState.onCreate (st : StreamState) (a : Id) (u : String) : StreamState :=
  { st with created := true, creator := keep st.creator a, url := keep st.url u, joined := addU a st.joined,
            admins := addU a st.admins }

/-- One accepted event. An event of another stream changes nothing. -/
def StreamState.step (st : StreamState) (e : Event) : StreamState :=
  if e.stream = st.stream then
    match e with
    | .streamCreate a _ u _ => st.onCreate a u.url
    | .principalInvite _ _ p _ => { st with joined := addU p st.joined }
    | .principalPromote _ _ p _ => { st with admins := addU p st.admins }
    | .principalDemote _ _ p _ => { st with admins := st.admins.filter (· != p) }
    | .principalBan _ _ p _ => { st with banned := addU p st.banned, admins := st.admins.filter (· != p) }
    | .streamPanic .. => { st with ended := true }
  else st

/-- The state of stream `s` after a log. -/
def fold (s : Id) (L : Log) : StreamState := L.foldl StreamState.step (StreamState.init s)

/-! ## Decisions from the state -/

def StreamState.member (st : StreamState) (p : Id) : Bool := st.joined.contains p && !st.banned.contains p
def StreamState.admin (st : StreamState) (p : Id) : Bool := st.member p && st.admins.contains p
def StreamState.otherAdmin (st : StreamState) (p : Id) : Bool := st.admins.any fun q => q != p && st.member q
def StreamState.mayAct (st : StreamState) (p : Id) : Bool := st.member p && !st.ended

/-- The rules' view of the stream, read from its state. -/
def StreamState.view (st : StreamState) : View :=
  ⟨st.created, st.ended, st.member, st.admin, st.banned.contains, st.otherAdmin⟩

/-- The first rule that fails, from the state. -/
def rejectionS (st : StreamState) (e : Event) : Option String := st.view.rejection e

/-! ## The state is the past, fact by fact

Each field of the state changes on one event exactly as the fact it stands for does (`step_*`), so folding a log
gives the fact over the whole log (`fold_*`). -/

theorem step_stream (st : StreamState) (e : Event) : (st.step e).stream = st.stream := by
  unfold StreamState.step; split
  · cases e <;> rfl
  · rfl

theorem step_created (st : StreamState) (e : Event) : (st.step e).created = (st.created || creates st.stream e) := by
  unfold StreamState.step; split <;> cases e <;> simp_all [StreamState.onCreate, creates, Event.stream]

theorem step_ended (st : StreamState) (e : Event) : (st.step e).ended = (st.ended || ends st.stream e) := by
  unfold StreamState.step; split <;> cases e <;> simp_all [StreamState.onCreate, ends, Event.stream]

theorem step_joined (st : StreamState) (e : Event) (p : Id) :
    (st.step e).joined.contains p = (st.joined.contains p || joins st.stream p e) := by
  unfold StreamState.step; split <;> cases e <;> simp_all [StreamState.onCreate, mem_addU, joins, Event.stream, beq_eq_decide]

theorem step_banned (st : StreamState) (e : Event) (p : Id) :
    (st.step e).banned.contains p = (st.banned.contains p || bans st.stream p e) := by
  unfold StreamState.step; split <;> cases e <;> simp_all [StreamState.onCreate, mem_addU, bans, Event.stream, beq_eq_decide]

theorem step_admins (st : StreamState) (e : Event) (p : Id) :
    (st.step e).admins.contains p = (adminRel st.stream p e).getD (st.admins.contains p) := by
  unfold StreamState.step; split <;> cases e <;>
    simp_all [StreamState.onCreate, mem_addU, List.mem_filter, adminRel, Event.stream] <;>
    (split <;> simp_all <;> (intro _ h; exact absurd h.symm ‹_›))

/-- A Boolean field that an event sets exactly when `f` says so folds to "some event says so". -/
theorem foldl_any {g : StreamState → Bool} {f : Id → Event → Bool}
    (hstep : ∀ st e, g (st.step e) = (g st || f st.stream e)) (st : StreamState) (L : Log) :
    g (L.foldl StreamState.step st) = (g st || L.any (f st.stream)) := by
  induction L generalizing st with
  | nil => simp
  | cons e es ih => simp [ih, hstep, step_stream, Bool.or_assoc]

theorem fold_any {g : StreamState → Bool} {f : Id → Event → Bool}
    (hstep : ∀ st e, g (st.step e) = (g st || f st.stream e)) (hinit : ∀ s, g (StreamState.init s) = false)
    (s : Id) (L : Log) : g (fold s L) = L.any (f s) := by
  rw [fold, foldl_any hstep, hinit]; simp [StreamState.init]

theorem latest_cons (e : Event) (L : Past) (rel : Event → Option Bool) :
    Past.latest (e :: L) rel = (Past.latest L rel).or (rel e) := by
  unfold Past.latest
  rw [← List.singleton_append, List.filterMap_append, List.getLast?_append]
  cases h : rel e <;> simp [h]

/-- A Boolean field that an event overrides when `rel` speaks folds to "what the latest event that speaks says". -/
theorem foldl_latest {g : StreamState → Bool} {rel : Id → Event → Option Bool}
    (hstep : ∀ st e, g (st.step e) = (rel st.stream e).getD (g st)) (st : StreamState) (L : Log) :
    g (L.foldl StreamState.step st) = (Past.latest L (rel st.stream)).getD (g st) := by
  induction L generalizing st with
  | nil => simp [Past.latest]
  | cons e es ih =>
    simp only [List.foldl_cons, ih, step_stream, hstep, latest_cons]
    cases Past.latest es (rel st.stream) <;> simp

/-! ### One lemma per fact the rules read -/

theorem fold_stream (s : Id) (L : Log) : (fold s L).stream = s := by
  unfold fold
  suffices ∀ st : StreamState, (L.foldl StreamState.step st).stream = st.stream from this _
  induction L with
  | nil => intro; rfl
  | cons e es ih => intro st; simp [List.foldl_cons, ih, step_stream]

theorem fold_created (s : Id) (L : Log) : (fold s L).created = Past.hasStream L s :=
  fold_any step_created (fun _ => rfl) s L

theorem fold_ended (s : Id) (L : Log) : (fold s L).ended = Past.ended L s :=
  fold_any step_ended (fun _ => rfl) s L

theorem fold_joined (s p : Id) (L : Log) : (fold s L).joined.contains p = Past.joined L s p :=
  fold_any (g := (·.joined.contains p)) (f := (joins · p)) (fun st e => step_joined st e p) (fun _ => rfl) s L

theorem fold_banned (s p : Id) (L : Log) : (fold s L).banned.contains p = Past.banned L s p :=
  fold_any (g := (·.banned.contains p)) (f := (bans · p)) (fun st e => step_banned st e p) (fun _ => rfl) s L

theorem fold_admins (s p : Id) (L : Log) :
    (fold s L).admins.contains p = (Past.latest L (adminRel s p)).getD false :=
  foldl_latest (g := (·.admins.contains p)) (rel := (adminRel · p)) (fun st e => step_admins st e p)
    (StreamState.init s) L

theorem fold_member (s p : Id) (L : Log) : (fold s L).member p = Past.member L s p := by
  rw [StreamState.member, fold_joined, fold_banned]; rfl

/-- The delicate one: an admin now is a member whose latest creation, promotion, demotion or ban made it one. -/
theorem fold_admin (s p : Id) (L : Log) : (fold s L).admin p = Past.admin L s p := by
  rw [StreamState.admin, fold_member, fold_admins]; rfl

theorem fold_mayAct (s p : Id) (L : Log) : (fold s L).mayAct p = Past.mayAct L s p := by
  rw [StreamState.mayAct, fold_member, fold_ended]; rfl

theorem latest_mem {l : Past} {rel : Event → Option Bool} {b : Bool} (h : Past.latest l rel = some b) :
    ∃ e ∈ l, rel e = some b := by
  unfold Past.latest at h
  have := List.mem_of_getLast? h
  simpa [List.mem_filterMap] using this

/-- An admin's latest word is "admin". -/
theorem admin_latest {L : Log} {t p : Id} (h : Past.admin L t p = true) : Past.latest L (adminRel t p) = some true := by
  simp only [Past.admin, Bool.and_eq_true] at h
  cases hl : Past.latest L (adminRel t p) with
  | none => simp [hl] at h
  | some b => cases b <;> simp_all

theorem otherAdmin_iff {L : Log} {s p : Id} :
    Past.otherAdmin L s p = true ↔ ∃ q, q ≠ p ∧ Past.admin L s q = true := by
  constructor
  · intro h
    obtain ⟨e, -, hx⟩ := List.any_eq_true.mp h
    cases e <;> simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at hx <;>
      first | exact ⟨_, hx.1.2, hx.2⟩ | simp at hx
  · rintro ⟨q, hne, hq⟩
    obtain ⟨e, he, hx⟩ := latest_mem (admin_latest hq)
    apply List.any_eq_true.mpr
    refine ⟨e, he, ?_⟩
    cases e <;> simp only [adminRel] at hx <;> (try split at hx) <;> (try cases hx) <;>
      (rename_i hc; simp only [Bool.and_eq_true, beq_iff_eq] at hc; obtain ⟨rfl, rfl⟩ := hc;
       simp [hne, hq])

theorem fold_otherAdmin (s p : Id) (L : Log) : (fold s L).otherAdmin p = Past.otherAdmin L s p := by
  rw [Bool.eq_iff_iff, otherAdmin_iff]
  simp only [StreamState.otherAdmin, List.any_eq_true, Bool.and_eq_true, bne_iff_ne, ne_eq]
  constructor
  · rintro ⟨q, hq, hne, hm⟩
    exact ⟨q, hne, by rw [← fold_admin]; simp [StreamState.admin, hm, hq]⟩
  · rintro ⟨q, hne, hq⟩
    rw [← fold_admin] at hq
    simp only [StreamState.admin, Bool.and_eq_true] at hq
    exact ⟨q, List.elem_iff.mp hq.2, hne, hq.1⟩

/-- **The state's view is the log's view.** No hypothesis: it holds for logs that are not valid too. -/
theorem fold_view (s : Id) (L : Log) : (fold s L).view = Past.view L s := by
  rw [StreamState.view, Past.view, fold_created, fold_ended, funext (fold_member s · L),
    funext (fold_admin s · L), funext (fold_banned s · L), funext (fold_otherAdmin s · L)]

/-! ## Deciding from the state is deciding from the log -/

theorem rejectionS_eq (L : Log) (e : Event) : rejectionS (fold e.stream L) e = rejection L e := by
  unfold rejectionS rejection; rw [fold_view]

/-- **Snapshots.** Folding the rest of a log onto the fold of its first part is folding the whole log. -/
theorem snapshot_equiv (s : Id) (L₁ L₂ : Log) : fold s (L₁ ++ L₂) = L₂.foldl StreamState.step (fold s L₁) := by
  simp [fold, List.foldl_append]

theorem fold_snoc (s : Id) (L : Log) (e : Event) : fold s (L ++ [e]) = (fold s L).step e := by
  simp [fold, List.foldl_append]

end StreamCore
