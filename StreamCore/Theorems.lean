-- Copyright (c) 2026 the proofbeta authors. All rights reserved. See LICENSE.
import StreamCore.Core

/-!
# What the stream guarantees

Every theorem is about a valid log and follows from the rules that held when its events were accepted.
-/

namespace StreamCore

/-- A rule of the list held for an accepted event. -/
theorem ok_rule {past : Past} {e : Event} (h : ok past e = true) {r : Rule} (hr : r ∈ rules) :
    r.holds (past.view e.stream) e = true :=
  (List.all_eq_true.mp h) r hr

/-! ## Minted ids are unique -/

/-- A creation in a valid log names a stream no earlier event created. -/
theorem create_fresh {pre post : Log} {c t : Id} {u : Creation} {m : Meta}
    (h : Valid (pre ++ Event.streamCreate c t u m :: post)) : Past.hasStream pre t = false := by
  have := ok_rule h.okAt (r := idTaken) (by simp [rules])
  simpa [idTaken, Past.view, Event.stream] using this

/-- The only event that mints an id is a creation, which mints its stream's. -/
theorem minted_create {e : Event} {x : Id} (hx : x ∈ e.mintedAll) : ∃ c u m, e = .streamCreate c x u m := by
  cases e <;> simp [Event.mintedAll] at hx
  subst hx; exact ⟨_, _, _, rfl⟩

/-- An id an event mints is minted by no other event of the log, before or after it. -/
theorem minted_once {log : Log} (h : Valid log) :
    ∀ a b e x, log = a ++ e :: b → x ∈ e.mintedAll → ∀ e' ∈ a ++ b, x ∉ e'.mintedAll := by
  intro a b e x hab hx e' he' hx'
  subst hab
  obtain ⟨c, u, m, rfl⟩ := minted_create hx
  obtain ⟨c', u', m', rfl⟩ := minted_create hx'
  rcases List.mem_append.mp he' with he' | he'
  · have h1 : Past.hasStream a x = true := List.any_eq_true.mpr ⟨_, he', by simp [creates]⟩
    rw [create_fresh h] at h1; cases h1
  · obtain ⟨b₁, b₂, rfl⟩ := List.append_of_mem he'
    have h1 : Past.hasStream (a ++ Event.streamCreate c x u m :: b₁) x = true :=
      List.any_eq_true.mpr ⟨Event.streamCreate c x u m, by simp, by simp [creates]⟩
    rw [create_fresh (by simpa using h)] at h1; cases h1

/-- Two events of a valid log that mint the same id are the same event. -/
theorem minted_same {log : Log} (h : Valid log) {e₁ e₂ : Event} {x : Id}
    (h₁ : e₁ ∈ log) (h₂ : e₂ ∈ log) (hx₁ : x ∈ e₁.mintedAll) (hx₂ : x ∈ e₂.mintedAll) : e₁ = e₂ := by
  obtain ⟨a, b, rfl⟩ := List.append_of_mem h₁
  simp only [List.mem_append, List.mem_cons] at h₂
  rcases h₂ with h₂ | rfl | h₂
  · exact absurd hx₂ (minted_once h a b e₁ x rfl hx₁ e₂ (List.mem_append_left _ h₂))
  · rfl
  · exact absurd hx₂ (minted_once h a b e₁ x rfl hx₁ e₂ (List.mem_append_right _ h₂))

/-- Minting is creating: `Past.minted` is `Past.hasStream`. -/
theorem minted_eq_hasStream (L : Log) (s : Id) : Past.minted L s = Past.hasStream L s := by
  unfold Past.minted Past.hasStream
  congr 1
  funext e
  cases e with
  | streamCreate a t u m =>
    by_cases h : t = s
    · subst h; simp [Event.mintedAll, creates]
    · simp [Event.mintedAll, creates, h, Ne.symm h]
  | _ => simp [Event.mintedAll, creates]

/-! ## A stream's creator and proof never change -/

/-- Two creations of the same stream id in a valid log have the same creator (first admin) and the same proof revision
URL (there is in fact only one: `minted_same`). -/
theorem stream_fixed {log : Log} (h : Valid log) {t a₁ a₂ : Id} {u₁ u₂ : Creation} {m₁ m₂ : Meta}
    (h₁ : Event.streamCreate a₁ t u₁ m₁ ∈ log) (h₂ : Event.streamCreate a₂ t u₂ m₂ ∈ log) : a₁ = a₂ ∧ u₁ = u₂ := by
  have := minted_same h h₁ h₂ (x := t) (by simp [Event.mintedAll]) (by simp [Event.mintedAll])
  simp at this
  exact ⟨this.1, this.2.1⟩

/-- **A stream exists iff it was created**: `Past.hasStream` read by its creation. -/
theorem hasStream_iff (past : Past) (t : Id) :
    Past.hasStream past t = true ↔ ∃ a u m, Event.streamCreate a t u m ∈ past := by
  simp only [Past.hasStream, List.any_eq_true]
  constructor
  · rintro ⟨e, he, hc⟩
    cases e <;> simp [creates] at hc
    subst hc; exact ⟨_, _, _, he⟩
  · rintro ⟨a, u, m, he⟩; exact ⟨_, he, by simp [creates]⟩

/-- A stream's proof names a full revision. -/
theorem stream_revision_valid {pre post : Log} {t a : Id} {u : Creation} {m : Meta}
    (h : Valid (pre ++ Event.streamCreate a t u m :: post)) : validRevisionUrl u.url = true :=
  ok_rule h.okAt (r := invalidRevisionUrl) (by simp [rules])

/-! ## A stream's proof can never change; to change the proof you start a new stream

`stream.create` is the only event that carries a proof revision URL (`Event`), and a stream id is created once
(`create_fresh`). So the revision of a stream is a function of the log, `proofRevision`, set by its creation and by
nothing else: once set it stays (`proof_revision_fixed`, for any log), every creation of the stream in a valid log
carries it (`proof_revision_unique`, `proof_revision_stays`), a creation after it names another stream
(`new_proof_new_stream`), and the engine's state and its reads show exactly it (`fold_url`). A layer cannot change it
either (`Layer.ValidX.proof_revision_unique`, `Layer.proof_revision_fixedX`): its events are not core events, and the
core's events of a valid combined log form a valid core log (`ValidX.base`). The host serves each stream only with the
engine built from its revision (README.md, "One revision per stream"). -/

/-- The proof revision URL of stream `t` in `log`: the URL its creation carries, or `none` if it was not created. -/
def proofRevision (log : Log) (t : Id) : Option String :=
  log.findSome? fun | .streamCreate _ t' u _ => if t' == t then some u.url else none | _ => none

theorem proofRevision_nil (t : Id) : proofRevision [] t = none := rfl

/-- **Once a stream has a revision, appending anything keeps it.** No hypothesis: it holds for logs that are not valid
too, so no later event, accepted or not, can change it. -/
theorem proof_revision_fixed {log : Log} {t : Id} {u : String} (h : proofRevision log t = some u) (post : Log) :
    proofRevision (log ++ post) t = some u := by
  unfold proofRevision at h ⊢
  rw [List.findSome?_append, h]; rfl

/-- A stream has a revision iff it was created. -/
theorem proofRevision_isSome (log : Log) (t : Id) : (proofRevision log t).isSome = Past.hasStream log t := by
  unfold proofRevision Past.hasStream
  induction log with
  | nil => rfl
  | cons e es ih =>
    rw [List.findSome?_cons, List.any_cons]
    cases e with
    | streamCreate a t' u m =>
      by_cases h : t' = t
      · subst h; simp [creates]
      · simp only [creates, beq_eq_decide, h, decide_false, Bool.false_or]; exact ih
    | _ => simpa [creates] using ih

/-- The revision is the URL of some creation of the stream. -/
theorem proofRevision_mem {log : Log} {t : Id} {u : String} (h : proofRevision log t = some u) :
    ∃ a c m, c.url = u ∧ Event.streamCreate a t c m ∈ log := by
  obtain ⟨e, he, hf⟩ := List.exists_of_findSome?_eq_some h
  cases e with
  | streamCreate a t' u' m =>
    simp only at hf
    split at hf
    · rename_i ht; simp only [beq_iff_eq] at ht; cases hf; subst ht; exact ⟨a, _, m, rfl, he⟩
    · cases hf
  | _ => simp at hf

/-- **In a valid log, every creation of a stream carries the stream's revision.** -/
theorem proof_revision_unique {log : Log} (h : Valid log) {a t : Id} {u : Creation} {m : Meta}
    (hc : Event.streamCreate a t u m ∈ log) : proofRevision log t = some u.url := by
  have hs : Past.hasStream log t = true := (hasStream_iff log t).mpr ⟨a, u, m, hc⟩
  rw [← proofRevision_isSome] at hs
  obtain ⟨u', hu'⟩ := Option.isSome_iff_exists.mp hs
  obtain ⟨a', c', m', rfl, hc'⟩ := proofRevision_mem hu'
  rw [hu', (stream_fixed h hc hc').2]

/-- **A stream's proof never changes**: once `log` gives stream `t` the revision `u`, any creation of `t` in any valid
continuation of `log` carries `u`. -/
theorem proof_revision_stays {log post : Log} (h : Valid (log ++ post)) {t : Id} {u : String}
    (hu : proofRevision log t = some u) {a : Id} {u' : Creation} {m : Meta}
    (hc : Event.streamCreate a t u' m ∈ log ++ post) : u'.url = u := by
  have := proof_revision_unique h hc
  rw [proof_revision_fixed hu post] at this
  exact (Option.some.inj this).symm

/-- **To change the proof you start a new stream**: a creation accepted after stream `t` has a revision names another
stream, whatever URL it carries. -/
theorem new_proof_new_stream {pre post : Log} {a t t' : Id} {u : String} {u' : Creation} {m : Meta}
    (h : Valid (pre ++ Event.streamCreate a t' u' m :: post)) (hu : proofRevision pre t = some u) : t' ≠ t := by
  rintro rfl
  have := proofRevision_isSome pre t'
  rw [hu, create_fresh h] at this
  cases this

theorem step_url (st : StreamState) (e : Event) :
    (st.step e).url = st.url.or (proofRevision [e] st.stream) := by
  unfold StreamState.step proofRevision
  split
  · rename_i hs
    cases e with
    | streamCreate a t u m =>
      simp only [Event.stream] at hs; subst hs
      cases h : st.url <;> simp [StreamState.onCreate, keep, h]
    | _ => cases st.url <;> simp
  · rename_i hs
    cases e with
    | streamCreate a t u m =>
      simp only [Event.stream] at hs
      cases st.url <;> simp [hs]
    | _ => cases st.url <;> simp

/-- **The fast path's revision is the log's**: the state the engine keeps for stream `t` (and a snapshot of it) holds
`proofRevision log t`, which is what a read of the stream shows as `proof_revision_url` (`Wire.streamSJ`). No
hypothesis. -/
theorem fold_url (t : Id) (log : Log) : (fold t log).url = proofRevision log t := by
  unfold fold
  suffices ∀ st : StreamState, (log.foldl StreamState.step st).url = st.url.or (proofRevision log st.stream) by
    rw [this]; rfl
  induction log with
  | nil => intro st; simp [proofRevision]
  | cons e es ih =>
    intro st
    rw [List.foldl_cons, ih, step_url, step_stream]
    have : proofRevision (e :: es) st.stream = (proofRevision [e] st.stream).or (proofRevision es st.stream) := by
      rw [← List.singleton_append]; unfold proofRevision; rw [List.findSome?_append]
    rw [this, Option.or_assoc]

/-! ## The latest word -/

theorem latest_snoc (l : Past) (e : Event) (rel : Event → Option Bool) :
    Past.latest (l ++ [e]) rel = (match rel e with | some b => some b | none => Past.latest l rel) := by
  unfold Past.latest
  rw [List.filterMap_append]
  cases h : rel e <;> simp [h, List.getLast?_append]

/-- The events that stop `q` being an admin of `t` are its demotion and its ban. -/
theorem rel_false {t q : Id} {e : Event} (h : adminRel t q e = some false) :
    ∃ a m, e = .principalDemote a t q m ∨ e = .principalBan a t q m := by
  cases e <;> simp only [adminRel] at h <;> (try split at h) <;> (try cases h) <;>
    (rename_i hc; simp only [Bool.and_eq_true, beq_iff_eq] at hc; obtain ⟨rfl, rfl⟩ := hc
     first | exact ⟨_, _, .inl rfl⟩ | exact ⟨_, _, .inr rfl⟩)

/-- A ban is the only event that bans: after `e`, `q` is banned from `t` only if it was before, or `e` bans it. -/
theorem banned_snoc {l : Past} {e : Event} {t q : Id} (h : Past.banned (l ++ [e]) t q = true) :
    Past.banned l t q = true ∨ ∃ a m, e = .principalBan a t q m := by
  simp only [Past.banned, List.any_append, Bool.or_eq_true, List.any_cons, List.any_nil, Bool.or_false] at h
  rcases h with h | h
  · exact .inl h
  · right; cases e <;> simp [bans] at h
    obtain ⟨rfl, rfl⟩ := h; exact ⟨_, _, rfl⟩

/-- An admin stays an admin across an event that is not its demotion or its ban. -/
theorem admin_keep {l : Past} {e : Event} {t q : Id} (h : Past.admin l t q = true)
    (h2 : adminRel t q e ≠ some false) : Past.admin (l ++ [e]) t q = true := by
  simp only [Past.admin, Past.member, Past.joined, Bool.and_eq_true, Bool.not_eq_true', List.any_append,
    Bool.or_eq_true] at h ⊢
  refine ⟨⟨.inl h.1.1, ?_⟩, ?_⟩
  · cases hb : Past.banned (l ++ [e]) t q
    · rfl
    · rcases banned_snoc hb with hb' | ⟨a, m, rfl⟩
      · rw [h.1.2] at hb'; cases hb'
      · exact absurd (by simp [adminRel]) h2
  · rw [latest_snoc]
    cases ha : adminRel t q e with
    | none => exact h.2
    | some b => cases b
                · exact absurd ha h2
                · rfl

/-! ## Only current admins act -/

/-- **Only current admins change membership or end a stream.** Every event but a creation, in a valid log, names a
stream created before it that had not ended, and was sent by a current admin of that stream. -/
theorem acts_by_admin {pre post : Log} {e : Event} {t : Id}
    (h : Valid (pre ++ e :: post)) (ht : e.stream = t) (hn : ∀ a t' u m, e ≠ .streamCreate a t' u m) :
    Past.hasStream pre t = true ∧ Past.ended pre t = false ∧ Past.admin pre t e.actor = true := by
  have hok := h.okAt
  have h1 := ok_rule hok (r := unknownStream) (by simp [rules])
  have h2 := ok_rule hok (r := streamEnded) (by simp [rules])
  have h3 := ok_rule hok (r := notStreamAdmin) (by simp [rules])
  subst ht
  cases e with
  | streamCreate a t' u m => exact absurd rfl (hn a t' u m)
  | _ => simp_all [unknownStream, streamEnded, notStreamAdmin, Past.view, Event.stream, Event.actor]

/-! ## Members and admins come from admins -/

/-- **Every member came from an admin.** Whoever is on a stream now, in a valid log, created the stream or was invited by
a principal that was then a current admin of the stream. -/
theorem members_by_admin {log : Log} (h : Valid log) {t p : Id} (hp : Past.member log t p = true) :
    (∃ u m, Event.streamCreate p t u m ∈ log) ∨
    (∃ pre post a m, log = pre ++ Event.principalInvite a t p m :: post ∧ Past.admin pre t a = true) := by
  simp only [Past.member, Past.joined, Bool.and_eq_true] at hp
  obtain ⟨e, he, hx⟩ := List.any_eq_true.mp hp.1
  cases e with
  | streamCreate a t' u m =>
    simp only [joins, Bool.and_eq_true, beq_iff_eq] at hx
    obtain ⟨rfl, rfl⟩ := hx
    exact .inl ⟨u, m, he⟩
  | principalInvite a t' p' m =>
    simp only [joins, Bool.and_eq_true, beq_iff_eq] at hx
    obtain ⟨rfl, rfl⟩ := hx
    obtain ⟨pre, post, rfl⟩ := List.append_of_mem he
    exact .inr ⟨pre, post, a, m, rfl, (acts_by_admin h rfl (by intros; simp)).2.2⟩
  | _ => simp [joins] at hx

/-- **The admin chain.** Whoever is an admin of a stream now, in a valid log, is on the stream, and created it or was
promoted by a principal that was then a current admin of the stream. -/
theorem admin_chain {log : Log} (h : Valid log) {t p : Id} (hp : Past.admin log t p = true) :
    Past.member log t p = true ∧
    ((∃ u m, Event.streamCreate p t u m ∈ log) ∨
     (∃ pre post a m, log = pre ++ Event.principalPromote a t p m :: post ∧ Past.admin pre t a = true)) := by
  refine ⟨by simp only [Past.admin, Bool.and_eq_true] at hp; exact hp.1, ?_⟩
  obtain ⟨e, he, hx⟩ := latest_mem (admin_latest hp)
  cases e with
  | streamCreate a t' u m =>
    simp only [adminRel] at hx
    split at hx
    · rename_i hc; simp only [Bool.and_eq_true, beq_iff_eq] at hc; obtain ⟨rfl, rfl⟩ := hc
      exact .inl ⟨u, m, he⟩
    · cases hx
  | principalPromote a t' p' m =>
    simp only [adminRel] at hx
    split at hx
    · rename_i hc; simp only [Bool.and_eq_true, beq_iff_eq] at hc; obtain ⟨rfl, rfl⟩ := hc
      obtain ⟨pre, post, rfl⟩ := List.append_of_mem he
      exact .inr ⟨pre, post, a, m, rfl, (acts_by_admin h rfl (by intros; simp)).2.2⟩
    · cases hx
  | principalDemote _ t' p' _ | principalBan _ t' p' _ =>
    simp only [adminRel] at hx; split at hx <;> cases hx
  | _ => simp [adminRel] at hx

/-! ## A stream always has an admin -/

/-- A ban names a stream the log already had. -/
theorem ban_has_stream {log : Log} (h : Valid log) {x t q : Id} {m : Meta}
    (hm : Event.principalBan x t q m ∈ log) : Past.hasStream log t = true := by
  obtain ⟨pre, post, rfl⟩ := List.append_of_mem hm
  have := (acts_by_admin h rfl (by intros; simp)).1
  simp only [Past.hasStream, List.any_append, Bool.or_eq_true] at *
  exact .inl this

/-- **Every stream of a valid log has a current admin**, at every point (apply it to each prefix: `Valid.prefix`). -/
theorem always_an_admin {log : Log} (h : Valid log) :
    ∀ t, Past.hasStream log t = true → ∃ a, Past.admin log t a = true := by
  induction h using Valid.induction with
  | nil => intro t ht; simp [Past.hasStream] at ht
  | @snoc l e hv hok ih =>
    intro t ht
    simp only [Past.hasStream, List.any_append, Bool.or_eq_true, List.any_cons, List.any_nil, Bool.or_false] at ht
    rcases ht with ht | ht
    · -- the stream already existed, with an admin `a`
      obtain ⟨a, ha⟩ := ih t ht
      cases hs : adminRel t a e with
      | some b =>
        cases b with
        | true => exact ⟨a, admin_keep ha (by simp [hs])⟩
        | false =>
          -- e demotes or bans `a`: by `last_admin`, another admin `q` remains, and e says nothing about `q`
          obtain ⟨x, m, he⟩ := rel_false hs
          have hla := ok_rule hok (r := lastAdmin) (by simp [rules])
          have hoth : Past.otherAdmin l t a = true := by
            rcases he with rfl | rfl <;> simpa [lastAdmin, Past.view, Event.stream, ha] using hla
          obtain ⟨e', -, hx⟩ := List.any_eq_true.mp hoth
          have mk : ∀ q, q ≠ a → Past.admin l t q = true → ∃ b, Past.admin (l ++ [e]) t b = true := by
            intro q hne hq
            refine ⟨q, admin_keep hq ?_⟩
            rcases he with rfl | rfl <;> simp [adminRel, Ne.symm hne]
          cases e' with
          | streamCreate q t' u m' =>
            simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hx
            exact mk q hx.1.2 hx.2
          | principalPromote y t' q m' =>
            simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hx
            exact mk q hx.1.2 hx.2
          | _ => simp at hx
      | none => exact ⟨a, admin_keep ha (by simp [hs])⟩
    · -- e creates the stream: its creator is a member and an admin, never banned before (the id is fresh)
      cases e <;> simp [creates] at ht
      rename_i a' t' u' m'
      subst ht
      refine ⟨a', ?_⟩
      have hnot : Past.hasStream l t' = false := create_fresh (post := []) (.snoc hv hok)
      have hnb : Past.banned l t' a' = false := by
        cases hb : Past.banned l t' a'
        · rfl
        · obtain ⟨e2, he2, hx2⟩ := List.any_eq_true.mp hb
          cases e2 <;> simp [bans] at hx2
          obtain ⟨rfl, rfl⟩ := hx2
          have := ban_has_stream hv he2
          simp [this] at hnot
      have hnb' : Past.banned (l ++ [Event.streamCreate a' t' u' m']) t' a' = false := by
        cases hb : Past.banned (l ++ [Event.streamCreate a' t' u' m']) t' a'
        · rfl
        · rcases banned_snoc hb with h' | ⟨_, _, h'⟩
          · simp [hnb] at h'
          · cases h'
      simp [Past.admin, Past.member, Past.joined, joins, hnb', latest_snoc, adminRel]

/-! ## An invite and a ban are both permanent -/

/-- **An invite is permanent.** Once invited, a principal is a member of the stream at every later point, unless and
until it is banned. -/
theorem invite_permanent {pre mid : Log} {a t p : Id} {m : Meta}
    (hnb : Past.banned (pre ++ Event.principalInvite a t p m :: mid) t p = false) :
    Past.member (pre ++ Event.principalInvite a t p m :: mid) t p = true := by
  simp [Past.member, Past.joined, joins, List.any_append, hnb]

/-- **A creation is permanent**, as an invite is: the creator of a stream is a member of it at every later point,
unless and until it is banned. -/
theorem create_permanent {pre mid : Log} {a t : Id} {u : Creation} {m : Meta}
    (hnb : Past.banned (pre ++ Event.streamCreate a t u m :: mid) t a = false) :
    Past.member (pre ++ Event.streamCreate a t u m :: mid) t a = true := by
  simp [Past.member, Past.joined, joins, List.any_append, hnb]

/-- **A promoted principal was a member** of the stream when it was promoted (the rule `not_member`). -/
theorem promote_member {pre post : Log} {a t p : Id} {m : Meta}
    (h : Valid (pre ++ Event.principalPromote a t p m :: post)) : Past.member pre t p = true := by
  have := ok_rule h.okAt (r := notMember) (by simp [rules])
  simpa [notMember, Past.view, Event.stream] using this

/-- **A ban is forever.** After a principal is banned from a stream, it is never a member of that stream again, and so
never an admin of it, at any later point. -/
theorem banned_stays_out {pre mid : Log} {a t p : Id} {m : Meta} :
    Past.member (pre ++ Event.principalBan a t p m :: mid) t p = false ∧
    Past.admin (pre ++ Event.principalBan a t p m :: mid) t p = false := by
  have hb : Past.banned (pre ++ Event.principalBan a t p m :: mid) t p = true := by
    simp [Past.banned, bans, List.any_append]
  have hm : Past.member (pre ++ Event.principalBan a t p m :: mid) t p = false := by simp [Past.member, hb]
  exact ⟨hm, by simp [Past.admin, hm]⟩

/-! ## Who may act on a stream: the contract with the layer above -/

/-- `mayAct` is current membership while the stream lasts. -/
theorem mayAct_iff_member (past : Past) (t p : Id) :
    Past.mayAct past t p = true ↔ Past.member past t p = true ∧ Past.ended past t = false := by
  simp [Past.mayAct]

/-- Right after an accepted invite of `p` on `t`, `p` may act on `t`. -/
theorem invite_grants_mayAct {pre : Log} {a t p : Id} {m : Meta}
    (h : Valid (pre ++ [Event.principalInvite a t p m])) :
    Past.mayAct (pre ++ [Event.principalInvite a t p m]) t p = true := by
  have hend := (acts_by_admin (post := []) h rfl (by intros; simp)).2.1
  have hb := ok_rule h.okAt (r := bannedRule) (by simp [rules])
  simp only [bannedRule, Past.view, Past.banned, Past.ended, Event.stream, Bool.not_eq_true'] at hb hend
  simp [Past.mayAct, Past.member, Past.joined, Past.banned, Past.ended, joins, bans, ends, List.any_append, hend, hb]

/-- After `p` is banned from `t`, it may never act on `t` again. -/
theorem ban_revokes_mayAct_forever {pre mid : Log} {a t p : Id} {m : Meta} :
    Past.mayAct (pre ++ Event.principalBan a t p m :: mid) t p = false := by
  simp [Past.mayAct, banned_stays_out.1]

/-- After a stream's panic, no principal may act on it, ever. -/
theorem panic_revokes_all {pre mid : Log} {a t : Id} {m : Meta} (q : Id) :
    Past.mayAct (pre ++ Event.streamPanic a t m :: mid) t q = false := by
  have : Past.ended (pre ++ Event.streamPanic a t m :: mid) t = true := by simp [Past.ended, ends, List.any_append]
  simp [Past.mayAct, this]

/-! ## Panic -/

/-- Every panic in a valid log was sent by a current admin of its stream. -/
theorem panic_by_admin {pre post : Log} {a t : Id} {m : Meta}
    (h : Valid (pre ++ Event.streamPanic a t m :: post)) : Past.admin pre t a = true :=
  (acts_by_admin h rfl (by intros; simp)).2.2

/-- A panic ends its stream: in a valid log, no event after a stream's panic names that stream. -/
theorem panic_ends_stream {pre mid post : Log} {a t : Id} {m : Meta} {e : Event}
    (h : Valid (pre ++ Event.streamPanic a t m :: mid ++ e :: post)) : e.stream ≠ t := by
  intro he
  have hs := ok_rule h.okAt (r := streamEnded) (by simp [rules])
  have hend : Past.ended (pre ++ Event.streamPanic a t m :: mid) t = true := by
    simp [Past.ended, ends, List.any_append]
  simp only [streamEnded, Past.view, he, hend, Bool.not_true] at hs
  cases hs

/-- A stream panics at most once. -/
theorem panic_once {pre mid post : Log} {a a' t : Id} {m m' : Meta}
    (h : Valid (pre ++ Event.streamPanic a t m :: mid ++ Event.streamPanic a' t m' :: post)) : False :=
  panic_ends_stream h rfl

/-! ## Kinds: only persons create streams

A creation records the kind of its creator as the host attests it (`Creation.kind`: `actor_kind`, a person when
absent), so the kind of a stream's creator is a fact of the stream's own events. What the rules add: -/

/-- **Only a person creates a stream** (the rule `creator_not_person`): the kind a creation records for its creator is
a person. -/
theorem creator_is_person {pre post : Log} {a t : Id} {u : Creation} {m : Meta}
    (h : Valid (pre ++ Event.streamCreate a t u m :: post)) : u.kind = .person := by
  have := ok_rule h.okAt (r := creatorNotPerson) (by simp [rules])
  simpa [creatorNotPerson] using this

/-- Every creation of a valid log records a person as its creator. -/
theorem creations_by_persons {log : Log} (h : Valid log) {a t : Id} {u : Creation} {m : Meta}
    (hc : Event.streamCreate a t u m ∈ log) : u.kind = .person := by
  obtain ⟨pre, post, rfl⟩ := List.append_of_mem hc
  exact creator_is_person h

/-!
## Not proved here (deliberately)

Everything above, and `CommandTheorems.lean`, `WireTheorems.lean` and the generic proofs of `Service.lean` at the core
(`Core.lean`), is about the functions `accept`, `check`, `toEvent`, `handle`, `run`, `stepJ` and `replayRows` and the
values they take. What follows stands between those
values and a running service, and is not proved. Each open gap has an id, `gap_<name>`. Where an assumption can be stated, it is the hypothesis of a theorem
rather than left implicit: `cas_refines_run` (gap_store_compare_and_set, gap_read_decide_append, gap_concurrency),
`toEvent_actor` (gap_token_is_caller), `replayFrom_ok` (gap_read_decide_append).

- **gap_wire_bytes. Bytes on the wire.** Statement: the `J` value the engine decodes is the JSON line the host sent,
  and the line it prints is the `J` it computed. Proved instead (`WireTheorems.lean`, `WireState.lean`, `Core.lean`): decoding
  inverts encoding for commands, requests, events, stored rows and states; whatever decodes is well formed; the
  engine's answer to a request is `responseToJ` of `respond` (`entryRequest_spec`). Not proved: our parser and
  printer in `Engine/Json.lean` (core Lean, no `partial`, no Lean JSON library; written to answer byte for byte as
  `Lean.Json.parse` and `Lean.Json.compress` of Lean v4.12.0 did), and the host's own JSON encoder.
- **gap_token_is_caller. The caller is the token's principal.** Statement: the caller the engine receives is the
  principal holding the bearer token. Proved instead: every event's actor is the caller (`toEvent_actor`), a stream's
  first admin is its creator (`toEvent_stream_iff`), and a command has no actor field. Why not proved: tokens are
  credentials in the host's store, not events.
- **gap_id_collisions. Stream ids rarely collide.** Statement: the host's UUIDv7s are distinct in practice. This is
  availability, not correctness: a repeated id is always refused with `id_taken` (`duplicate_refused`), and a refusal
  never changes the log (`refused_keeps_log`).
- **gap_storage_durability. Storage is durable and atomic.** Statement: an append the host reports is on disk, whole,
  and never changed. Why not proved: the host's store and the disks under it are outside the model.
- **gap_store_compare_and_set. The store's `append_batch` is `attemptBatch`'s compare-and-set.** Statement:
  `append_batch(s, n, rows)` commits exactly when stream `s` has exactly `n` rows, storing the rows at `n, n+1, ...`,
  and otherwise stores nothing. Why not proved: the store is outside the model.
- **gap_read_decide_append. The read-decide-append glue is `attemptBatch`.** Statement: for each batch, the host's
  stream owner syncs the stream into the engine up to the store's length `n`, the engine decides the requests one
  after another from the entry of those `n` events, and the owner appends the accepted events at `n` (on a failed
  append: forget the stream, decide again). Proved: the protocol (`cas_refines_run`, `batch_refines_run`,
  `batch_answer`); the engine's bookkeeping for each step (`entryRequest_spec`, `entrySync_spec`); deciding on the
  stream is deciding on the whole log (`respond_local`). Not proved: that the host's glue implements
  `attemptBatch`, and the hash map in `Engine/Step.lean` that holds the entries.
- **gap_compiled_engine. The compiled engine is the proved functions.** Statement: the machine code of
  `stream-engine` computes `entryRequest`, `entrySync`, `stepS`, `replaySFrom`, and, on the audit path,
  `replayRows` and `check`. Why not proved: the kernel checks proofs about terms; the Lean compiler, the C compiler,
  the Lean runtime, and the `@[extern]` primitives and `@[csimp]` replacements the functions reach (pinned by
  `scripts/Audit.lean`) are trusted.
- **gap_runtime_failures. No runtime failure changes an answer.** (Lean's `panic!` and the runtime, not the
  `stream.panic` event.) Checked, not proved: no constant through which compiled code panics is reachable from the
  decision and wire functions (`scripts/Audit.lean`). What remains: the parser, the runtime (memory, stack) and the IO
  loop.
- **gap_concurrency. Concurrent requests form one sequence per stream.** Statement: under concurrency, in one process
  or many, each stream's rows are a sequence of batches, each decided one request at a time. Proved: under any
  interleaving of batches with compare-and-set appends, each stream is `run` of its committed batches' requests in
  commit order and the delivered answers are `run`'s (`cas_refines_run`).
- **gap_read_visibility. Who may read what.** Statement: reads reveal what they should. Why not proved: visibility is
  not in the model.
- **gap_no_unsafe_declarations. The decision and wire functions use no `partial`, `unsafe`, `implemented_by`, `extern`
  or `native_decide` of ours.** Why not proved: a fact about declarations, not a proposition of the logic.
- **gap_principal_issuance. Principal identity and token issuance.** Statement: every principal id in the log is one
  some person or agent can authenticate as, and only they. Why not proved: the model has no principals of its own.
- **gap_kind_issuance. A creator's attested kind is what it is.** Statement: the `actor_kind` a creation records is
  the kind of the principal behind the caller's credential (absent: a person). Proved instead: the kind is recorded in
  the creation event, and a creation recording an agent is refused (`creator_is_person`, `creations_by_persons`), so
  every theorem about a creator's kind follows from the stream's own events. Why not proved: who is behind a
  credential is outside the model, as for gap_token_is_caller; the host attests the kind from its principal table,
  where it is set when the principal is issued and never changed.
- **gap_after_panic. Continuing after a panic.** Deliberately not in this core: a panic ends a stream for good
  (`panic_ends_stream`); continuing means a new stream and a catch-up by the layer above.
- **gap_layer_above_contract. The layer above keeps the contract.** Statement: for every event `E` the layer above
  appends to stream `t`'s stream, at the point where the log is `L`, `Past.mayAct L t E.actor = true`. Why
  not proved here: the layer above's events are not in this core. Proved here: what `mayAct` is and how invite, ban
  and panic change it (`mayAct_iff_member`, `invite_grants_mayAct`, `invite_permanent`, `ban_revokes_mayAct_forever`,
  `panic_revokes_all`), and that the engine's `may_act` is it (`mem_membersS`, `fold_mayAct`).
- **gap_unproved_edge. The compiled code is the kernel's code, and the unproved edge stays small.** Statement: what
  the compiler runs is the definitions the kernel checked, and the unproved edge (`parseLine`, `render`, the entry map
  and message dispatch of `Engine/Step.lean` and its loop `Engine.serve`) does what it says. Why not proved: `#print
  axioms` and the dependency audit walk kernel terms; the compiler substitutes `@[csimp]` replacements and `@[extern]`
  primitives; the edge is our JSON parser and printer and `Std.HashMap`, neither proved.
- **gap_engine_is_revision. The engine judging a stream was built from the stream's revision.** Statement: every
  request on stream `t`, and every stored row of `t` replayed or checked, is decided by an engine compiled from the
  commit that `proofRevision log t` names. Proved instead: a stream's revision is set by its creation and never
  changes, whatever is appended, by the core or by any layer (`proof_revision_fixed`, `proof_revision_unique`,
  `proof_revision_stays`, `new_proof_new_stream`, `Layer.ValidX.proof_revision_unique`), and the engine's state and
  reads show it (`fold_url`). Why not proved: which binary runs is a fact about the build and the deploy, outside the
  logic. The host sends a stream only to the engine configured for its revision, and checks at startup that each
  engine reports that revision (`{"query":"revision"}`); the report is a constant written into the build from `git
  rev-parse` (`scripts/stamp_revision`), trusted, not checked against the source it was compiled from.
- **gap_snapshot_fold. A stored snapshot is the fold of the rows it names.** Statement: a stored snapshot `(s, k,
  state, hash)` has `state = fold s (first k events of s)`. Proved instead: if it is, deciding from it and the rows
  after it is deciding from the whole stream (`snapshot_equiv`, `snapshot_sound`), and a state survives encoding
  (`stateFromJ_toJ`).
-/

end StreamCore
