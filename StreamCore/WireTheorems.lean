-- Copyright (c) 2026 the proofbeta authors. All rights reserved. See LICENSE.
import StreamCore.Wire

/-!
# The wire, proved

Decoding inverts encoding on well-formed values; whatever decodes is well formed; reads answer the rules' predicates.
Stored rows, forms over `run` and the startup replay are proved once for every service (`Service.lean`) and given to
the core in `Core.lean`.
-/

namespace StreamCore.Wire
open StreamCore

/-! ## Decoding inverts encoding -/

theorem checked_ok {α} {w : String} {wf : α → Bool} {x : α} (h : wf x = true) : checked w wf x = .ok x := by
  simp [checked, h]

theorem checked_wf {α} {w : String} {wf : α → Bool} {x y : α} (h : checked w wf x = .ok y) : wf y = true := by
  unfold checked at h
  split at h
  · cases h; assumption
  · cases h

/-- A well-formed command survives encoding and decoding unchanged. -/
theorem commandFromJ_toJ (cmd : Command) (h : commandWf cmd = true) : commandFromJ (commandToJ cmd) = .ok cmd := by
  have hc := checked_ok (w := "command") h
  cases cmd
  case streamCreate c m => obtain ⟨u, _ | _ | _⟩ := c <;> cases m <;>
    simp_all [commandFromJ, commandToJ, actorKindJ, actorKindOf, kindJ, fields, str, onlyKeys, get?, metaOf,
      List.find?, bind, Except.bind, pure, Except.pure, metaJ]
  all_goals (rename_i m; cases m) <;>
    simp_all [commandFromJ, commandToJ, changeCommandJ, fields, str, onlyKeys, get?, metaOf, changeCommand,
      List.find?, bind, Except.bind, pure, Except.pure, metaJ]

theorem strs_toJ (what : String) (l : List String) : strs what (.arr (l.map .str)) = .ok l := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [strs, List.map_cons, List.mapM_cons] at ih ⊢
    simp [ih, bind, Except.bind, pure, Except.pure]

/-- A well-formed request survives encoding and decoding unchanged. -/
theorem requestFromJ_toJ (r : Request) (h : requestWf r = true) : requestFromJ (requestToJ r) = .ok r := by
  obtain ⟨c, cmd, f⟩ := r
  have hcmd : commandWf cmd = true := by simp_all [requestWf]
  have hr := checked_ok (w := "request") h
  simp_all [requestFromJ, requestToJ, fields, onlyKeys, get?, List.find?, callerFromJ, str, commandFromJ_toJ cmd hcmd,
    freshFromJ, strs_toJ, bind, Except.bind]

/-- A well-formed event survives encoding and decoding unchanged. -/
theorem eventFromJ_toJ (e : Event) (h : eventWf e = true) : eventFromJ (eventToJ e) = .ok e := by
  have hc := checked_ok (w := "event") h
  cases e
  case streamCreate a t c m => obtain ⟨u, _ | _ | _⟩ := c <;> cases m <;>
    simp_all [eventFromJ, eventToJ, actorKindJ, actorKindOf, kindJ, fields, str, onlyKeys, get?, metaOf,
      List.find?, bind, Except.bind, pure, Except.pure, metaJ]
  all_goals (rename_i m; cases m) <;>
    simp_all [eventFromJ, eventToJ, changeEventJ, fields, str, onlyKeys, get?, metaOf, changeEvent, List.find?,
      bind, Except.bind, pure, Except.pure, metaJ]

/-! ## Whatever decodes is well formed -/

theorem commandFromJ_wf {j : J} {cmd : Command} (h : commandFromJ j = .ok cmd) : commandWf cmd = true := by
  unfold commandFromJ at h
  simp only [bind, Except.bind] at h
  repeat (first | (split at h <;> try contradiction) | exact checked_wf h)

theorem requestFromJ_wf {j : J} {r : Request} (h : requestFromJ j = .ok r) : requestWf r = true := by
  unfold requestFromJ at h
  simp only [bind, Except.bind] at h
  repeat (first | (split at h <;> try contradiction) | exact checked_wf h)

theorem eventFromJ_wf {j : J} {e : Event} (h : eventFromJ j = .ok e) : eventWf e = true := by
  unfold eventFromJ at h
  simp only [bind, Except.bind] at h
  repeat (first | (split at h <;> try contradiction) | exact checked_wf h)

/-- A well-formed request translates to a well-formed event. -/
theorem toEvent_wf {c : Id} {cmd : Command} {f : Fresh} {e : Event} (hr : requestWf (c, cmd, f) = true)
    (h : toEvent c cmd f = .ok e) : eventWf e = true := by
  rw [eventWf, toRequest_toEvent h]; exact hr

/-! ## Reads -/

theorem mem_dedup {x : Id} {l : List Id} : x ∈ dedup l ↔ x ∈ l := by
  induction l with
  | nil => simp [dedup]
  | cons y ys ih =>
    unfold dedup
    split
    · rename_i hc
      simp only [List.mem_cons, List.mem_filter, ih, bne_iff_ne, ne_eq]
      constructor
      · rintro (h | ⟨h, -⟩) <;> simp_all
      · rintro (h | h)
        · exact .inl h
        · by_cases hxy : x = y
          · exact .inl hxy
          · exact .inr ⟨h, hxy⟩
    · simp [ih]

theorem member_named {log : Log} {t p : Id} (h : Past.member log t p = true) : p ∈ log.filterMap (named t) := by
  simp only [Past.member, Past.joined, Bool.and_eq_true] at h
  obtain ⟨e, he, hx⟩ := List.any_eq_true.mp h.1
  rw [List.mem_filterMap]
  refine ⟨e, he, ?_⟩
  cases e <;> simp_all [named, joins]

/-- **Reads answer exactly the rules' predicates.** An entry is in the member list of stream `t` exactly when its
principal is a current member, and then its flags are `Past.admin` and `Past.mayAct`. -/
theorem mem_members {log : Log} {t : Id} {x : Id × Bool × Bool} :
    x ∈ members log t ↔
      Past.member log t x.1 = true ∧ x.2.1 = Past.admin log t x.1 ∧ x.2.2 = Past.mayAct log t x.1 := by
  obtain ⟨p, a, m⟩ := x
  simp only [members, List.mem_map, List.mem_filter, mem_dedup, Prod.mk.injEq]
  constructor
  · rintro ⟨q, ⟨-, hq⟩, rfl, rfl, rfl⟩; exact ⟨hq, rfl, rfl⟩
  · rintro ⟨hm, rfl, rfl⟩; exact ⟨p, ⟨member_named hm, hm⟩, rfl, rfl, rfl⟩

end StreamCore.Wire
