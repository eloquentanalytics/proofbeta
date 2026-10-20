-- Copyright (c) 2026 the proofbeta authors. All rights reserved. See LICENSE.
import StreamCore.Interface

/-!
# structured_meta: a typed `meta` inside `ewm1.`, with its proofs

The core carries `meta : Option String` on every command and event and checks only its form (`validMeta`: `ewm1.`,
then base64url, at most 4096 bytes; `wfMeta`: and no U+0000). This file gives the body a structure:

- **The format.** `ewm1.` then the unpadded base64url (RFC 4648 §5) of a payload of bytes: a version byte `1`, then
  each field as its key and its value, each a two-byte big-endian length and that many bytes of UTF-8. Keys are
  `[a-z0-9_]`, 1 to 64 characters, strictly ascending, so a meta value is a finite map with one written form.
- **The proofs.** base64url round trip and canonicality (`b64dec_enc`, `b64enc_dec`); `decode (encode m) = some m`
  for every well-formed `m` that fits (`decode_encode`); whatever decodes is well formed and fits (`decode_wf`), and
  is encoded back to exactly the string it came from (`encode_decode`), so `decode` is injective (`decode_inj`) and
  `encode` its only preimage; every encoded value is a legal core meta (`wfMeta_encode`), with its size exactly
  `5 + ⌈4n/3⌉` bytes for a payload of `n` bytes (`encode_size`), so it is legal iff `n ≤ 3068` (`validMeta_encode_iff`).
- **Meta on events.** `eventMeta`, `commandMeta` for the core's six; `toEvent_meta_of`: through any service's
  command/event bijection, an event's meta is its command's.
- **Schemas.** A schema is a list of fields (key, kind, required); `conforms` checks a value against one: every
  required key present, no key outside the schema, each value of its kind (`text`: non-empty; `url`: an absolute URL;
  `uuid`: the core's `validUuid`).

The core's `validMeta`/`wfMeta` are printed as signatures in the interface. `validMeta_eq`/`wfMeta_some` restate them
as their docstrings say, by `rfl`: the one place this file reads a body the interface does not print (the boundary
check sees constants, not definitional unfolding; a `validMeta_iff` in the interface would replace it).
-/

namespace Work
open StreamCore StreamCore.Wire

/-! ## base64url, unpadded -/

/-- The base64url alphabet: `A`–`Z`, `a`–`z`, `0`–`9`, `-`, `_` for 0 to 63. -/
def sextetChar (i : Nat) : Char :=
  if i < 26 then Char.ofNat (65 + i)
  else if i < 52 then Char.ofNat (97 + (i - 26))
  else if i < 62 then Char.ofNat (48 + (i - 52))
  else if i = 62 then '-' else '_'

/-- A base64url character's value. -/
def charSextet (c : Char) : Option Nat :=
  if 65 ≤ c.toNat ∧ c.toNat ≤ 90 then some (c.toNat - 65)
  else if 97 ≤ c.toNat ∧ c.toNat ≤ 122 then some (c.toNat - 97 + 26)
  else if 48 ≤ c.toNat ∧ c.toNat ≤ 57 then some (c.toNat - 48 + 52)
  else if c = '-' then some 62
  else if c = '_' then some 63 else none

theorem charSextet_sextetChar_fin : ∀ i : Fin 64, charSextet (sextetChar i) = some i := by decide

theorem charSextet_sextetChar {i : Nat} (h : i < 64) : charSextet (sextetChar i) = some i :=
  charSextet_sextetChar_fin ⟨i, h⟩

theorem sextetChar_charSextet {c : Char} {i : Nat} (h : charSextet c = some i) : i < 64 ∧ sextetChar i = c := by
  unfold charSextet at h
  have hc := Char.ofNat_toNat c
  split at h
  · cases h; refine ⟨by omega, ?_⟩
    simp only [sextetChar, show c.toNat - 65 < 26 by omega, ↓reduceIte]
    rw [show 65 + (c.toNat - 65) = c.toNat by omega, hc]
  split at h
  · cases h; refine ⟨by omega, ?_⟩
    simp only [sextetChar, show ¬ c.toNat - 97 + 26 < 26 by omega, show c.toNat - 97 + 26 < 52 by omega,
      ↓reduceIte]
    rw [show 97 + (c.toNat - 97 + 26 - 26) = c.toNat by omega, hc]
  split at h
  · cases h; refine ⟨by omega, ?_⟩
    simp only [sextetChar, show ¬ c.toNat - 48 + 52 < 26 by omega, show ¬ c.toNat - 48 + 52 < 52 by omega,
      show c.toNat - 48 + 52 < 62 by omega, ↓reduceIte]
    rw [show 48 + (c.toNat - 48 + 52 - 52) = c.toNat by omega, hc]
  split at h
  · cases h; subst_vars; decide
  split at h
  · cases h; subst_vars; decide
  · cases h

/-- Three bytes, four characters. -/
def enc3 (n : Nat) : List Char :=
  [sextetChar (n / 262144), sextetChar (n / 4096 % 64), sextetChar (n / 64 % 64), sextetChar (n % 64)]

/-- **base64url, unpadded**: each three bytes four characters; two bytes left three characters, one byte left two
(the unused low bits zero). -/
def b64enc : List UInt8 → List Char
  | a :: b :: c :: rest => enc3 (a.toNat * 65536 + b.toNat * 256 + c.toNat) ++ b64enc rest
  | [a, b] => let n := a.toNat * 256 + b.toNat
    [sextetChar (n / 1024), sextetChar (n / 16 % 64), sextetChar (n % 16 * 4)]
  | [a] => [sextetChar (a.toNat / 4), sextetChar (a.toNat % 4 * 16)]
  | [] => []

/-- **Its inverse**, canonical only: no `=`, no length `4k + 1`, the unused low bits zero; `none` otherwise. -/
def b64dec : List Char → Option (List UInt8)
  | c0 :: c1 :: c2 :: c3 :: rest =>
    match charSextet c0, charSextet c1, charSextet c2, charSextet c3, b64dec rest with
    | some s0, some s1, some s2, some s3, some r =>
      let n := s0 * 262144 + s1 * 4096 + s2 * 64 + s3
      some (UInt8.ofNat (n / 65536) :: UInt8.ofNat (n / 256 % 256) :: UInt8.ofNat (n % 256) :: r)
    | _, _, _, _, _ => none
  | [c0, c1, c2] =>
    match charSextet c0, charSextet c1, charSextet c2 with
    | some s0, some s1, some s2 =>
      if s2 % 4 = 0 then
        let n := s0 * 4096 + s1 * 64 + s2
        some [UInt8.ofNat (n / 1024), UInt8.ofNat (n / 4 % 256)]
      else none
    | _, _, _ => none
  | [c0, c1] =>
    match charSextet c0, charSextet c1 with
    | some s0, some s1 => if s1 % 16 = 0 then some [UInt8.ofNat (s0 * 4 + s1 / 16)] else none
    | _, _ => none
  | [_] => none
  | [] => some []

theorem uint8_eq {x : UInt8} {k : Nat} (h : k = x.toNat) : UInt8.ofNat k = x := by
  subst h; exact UInt8.ofNat_toNat

theorem toNat_ofNat_lt {k : Nat} (h : k < 256) : (UInt8.ofNat k).toNat = k := by
  simp; omega

/-- **base64url round trip.** -/
theorem b64dec_enc (l : List UInt8) : b64dec (b64enc l) = some l := by
  induction l using b64enc.induct with
  | case1 a b c rest ih =>
    have ha := UInt8.toNat_lt a; have hb := UInt8.toNat_lt b; have hc := UInt8.toNat_lt c
    simp only [b64enc, enc3, List.cons_append, List.nil_append, b64dec]
    rw [charSextet_sextetChar (by omega), charSextet_sextetChar (by omega), charSextet_sextetChar (by omega),
      charSextet_sextetChar (by omega), ih]
    simp only [Option.some.injEq, List.cons.injEq]
    refine ⟨uint8_eq (by omega), uint8_eq (by omega), uint8_eq (by omega), trivial⟩
  | case2 a b =>
    have ha := UInt8.toNat_lt a; have hb := UInt8.toNat_lt b
    simp only [b64enc, b64dec]
    rw [charSextet_sextetChar (by omega), charSextet_sextetChar (by omega), charSextet_sextetChar (by omega)]
    simp only [show (a.toNat * 256 + b.toNat) % 16 * 4 % 4 = 0 by omega, ↓reduceIte, Option.some.injEq,
      List.cons.injEq]
    refine ⟨uint8_eq (by omega), uint8_eq (by omega), trivial⟩
  | case3 a =>
    have ha := UInt8.toNat_lt a
    simp only [b64enc, b64dec]
    rw [charSextet_sextetChar (by omega), charSextet_sextetChar (by omega)]
    simp only [show a.toNat % 4 * 16 % 16 = 0 by omega, ↓reduceIte, Option.some.injEq, List.cons.injEq]
    exact ⟨uint8_eq (by omega), trivial⟩
  | case4 => rfl

theorem enc3_sextets {s0 s1 s2 s3 : Nat} (h0 : s0 < 64) (h1 : s1 < 64) (h2 : s2 < 64) (h3 : s3 < 64) :
    let n := s0 * 262144 + s1 * 4096 + s2 * 64 + s3
    enc3 ((UInt8.ofNat (n / 65536)).toNat * 65536 + (UInt8.ofNat (n / 256 % 256)).toNat * 256 +
      (UInt8.ofNat (n % 256)).toNat) = [sextetChar s0, sextetChar s1, sextetChar s2, sextetChar s3] := by
  intro n
  rw [toNat_ofNat_lt (by omega), toNat_ofNat_lt (by omega), toNat_ofNat_lt (by omega)]
  have e : n / 65536 * 65536 + n / 256 % 256 * 256 + n % 256 = n := by omega
  simp only [enc3, e]
  have a0 : n / 262144 = s0 := by omega
  have a1 : n / 4096 % 64 = s1 := by omega
  have a2 : n / 64 % 64 = s2 := by omega
  have a3 : n % 64 = s3 := by omega
  rw [a0, a1, a2, a3]

/-- **base64url is canonical**: what decodes is encoded back to exactly the characters it came from. -/
theorem b64enc_dec : ∀ {cs : List Char} {l : List UInt8}, b64dec cs = some l → b64enc l = cs
  | c0 :: c1 :: c2 :: c3 :: rest, l, h => by
    simp only [b64dec] at h
    split at h
    · rename_i s0 s1 s2 s3 r h0 h1 h2 h3 hr
      cases h
      obtain ⟨l0, e0⟩ := sextetChar_charSextet h0; obtain ⟨l1, e1⟩ := sextetChar_charSextet h1
      obtain ⟨l2, e2⟩ := sextetChar_charSextet h2; obtain ⟨l3, e3⟩ := sextetChar_charSextet h3
      simp only [b64enc, b64enc_dec hr, enc3_sextets l0 l1 l2 l3, e0, e1, e2, e3]
      rfl
    · cases h
  | [c0, c1, c2], l, h => by
    simp only [b64dec] at h
    split at h
    · rename_i s0 s1 s2 h0 h1 h2
      obtain ⟨l0, e0⟩ := sextetChar_charSextet h0; obtain ⟨l1, e1⟩ := sextetChar_charSextet h1
      obtain ⟨l2, e2⟩ := sextetChar_charSextet h2
      split at h
      · rename_i hz
        cases h
        simp only [b64enc]
        rw [toNat_ofNat_lt (by omega), toNat_ofNat_lt (by omega)]
        have a0 : ((s0 * 4096 + s1 * 64 + s2) / 1024 * 256 + (s0 * 4096 + s1 * 64 + s2) / 4 % 256) / 1024 = s0 := by
          omega
        have a1 : ((s0 * 4096 + s1 * 64 + s2) / 1024 * 256 + (s0 * 4096 + s1 * 64 + s2) / 4 % 256) / 16 % 64 = s1 := by
          omega
        have a2 : ((s0 * 4096 + s1 * 64 + s2) / 1024 * 256 + (s0 * 4096 + s1 * 64 + s2) / 4 % 256) % 16 * 4 = s2 := by
          omega
        rw [a0, a1, a2, e0, e1, e2]
      · cases h
    · cases h
  | [c0, c1], l, h => by
    simp only [b64dec] at h
    split at h
    · rename_i s0 s1 h0 h1
      obtain ⟨l0, e0⟩ := sextetChar_charSextet h0; obtain ⟨l1, e1⟩ := sextetChar_charSextet h1
      split at h
      · cases h
        simp only [b64enc]
        rw [toNat_ofNat_lt (by omega)]
        have a0 : (s0 * 4 + s1 / 16) / 4 = s0 := by omega
        have a1 : (s0 * 4 + s1 / 16) % 4 * 16 = s1 := by omega
        rw [a0, a1, e0, e1]
      · cases h
    · cases h
  | [c], l, h => by simp [b64dec] at h
  | [], l, h => by cases h; rfl

/-- Every character of an encoding is one of the alphabet's. -/
theorem b64enc_mem {l : List UInt8} {c : Char} (h : c ∈ b64enc l) : ∃ i < 64, sextetChar i = c := by
  induction l using b64enc.induct with
  | case1 a b x rest ih =>
    have ha := UInt8.toNat_lt a; have hb := UInt8.toNat_lt b; have hx := UInt8.toNat_lt x
    simp only [b64enc, enc3, List.cons_append, List.nil_append, List.mem_cons] at h
    rcases h with h | h | h | h | h
    · exact ⟨_, by omega, h.symm⟩
    · exact ⟨_, by omega, h.symm⟩
    · exact ⟨_, by omega, h.symm⟩
    · exact ⟨_, by omega, h.symm⟩
    · exact ih h
  | case2 a b =>
    have ha := UInt8.toNat_lt a; have hb := UInt8.toNat_lt b
    simp only [b64enc, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h
    · exact ⟨_, by omega, h.symm⟩
    · exact ⟨_, by omega, h.symm⟩
    · exact ⟨_, by omega, h.symm⟩
  | case3 a =>
    have ha := UInt8.toNat_lt a
    simp only [b64enc, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h
    · exact ⟨_, by omega, h.symm⟩
    · exact ⟨_, by omega, h.symm⟩
  | case4 => simp [b64enc] at h

/-- The length of an encoding: `⌈4n/3⌉` characters for `n` bytes. -/
theorem b64enc_length (l : List UInt8) : (b64enc l).length = (4 * l.length + 2) / 3 := by
  induction l using b64enc.induct with
  | case1 a b c rest ih => simp only [b64enc, enc3, List.length_append, ih, List.length_cons, List.length_nil]; omega
  | case2 a b => simp [b64enc]
  | case3 a => simp [b64enc]
  | case4 => rfl

/-! ## Strings as UTF-8 bytes -/

/-- A string's UTF-8 bytes. -/
def strBytes (s : String) : List UInt8 := s.toByteArray.data.toList

/-- UTF-8 bytes as a string: `none` unless they are valid UTF-8. -/
def strOfBytes (bs : List UInt8) : Option String :=
  (ByteArray.mk bs.toArray).utf8Decode?.map fun a => String.ofList a.toList

theorem strOfBytes_strBytes (s : String) : strOfBytes (strBytes s) = some s := by
  have hb : ByteArray.mk s.toByteArray.data.toList.toArray = s.toList.utf8Encode := by
    rw [String.utf8Encode_toList]
  rw [strOfBytes, strBytes, hb, List.utf8Decode?_utf8Encode]
  simp [String.ofList_toList]

theorem strBytes_strOfBytes {bs : List UInt8} {s : String} (h : strOfBytes bs = some s) : strBytes s = bs := by
  simp only [strOfBytes, Option.map_eq_some_iff] at h
  obtain ⟨a, ha, rfl⟩ := h
  have hs : (ByteArray.mk bs.toArray).utf8Decode?.isSome = true := by rw [ha]; rfl
  have := ByteArray.utf8Encode_get_utf8Decode? (h := hs)
  simp only [ha, Option.get_some] at this
  simp [strBytes, String.toByteArray_ofList, this]

/-! ## The payload: a version byte, then each field's key and value, length-prefixed -/

/-- A structured meta value: its fields, keys ascending. -/
abbrev MetaValue := List (String × String)

/-- A length as two bytes, big-endian. -/
def u16 (n : Nat) : List UInt8 := [UInt8.ofNat (n / 256), UInt8.ofNat (n % 256)]

/-- A string, length-prefixed. -/
def field (s : String) : List UInt8 := u16 (strBytes s).length ++ strBytes s

/-- The fields, each key then value. -/
def entries : MetaValue → List UInt8
  | [] => []
  | (k, v) :: rest => field k ++ field v ++ entries rest

/-- The version of this format: the payload's first byte. -/
def version : UInt8 := 1

/-- The payload: the version byte, then the fields. -/
def payload (m : MetaValue) : List UInt8 := version :: entries m

/-- One length-prefixed string off the front, and the rest. -/
def takeField : List UInt8 → Option (String × List UInt8)
  | hi :: lo :: rest =>
    let n := hi.toNat * 256 + lo.toNat
    if n ≤ rest.length then (strOfBytes (rest.take n)).map fun s => (s, rest.drop n) else none
  | _ => none

/-- The fields of a payload (after its version byte); `fuel` bounds the number of fields. -/
def parseEntries : Nat → List UInt8 → Option MetaValue
  | _, [] => some []
  | 0, _ :: _ => none
  | f + 1, b :: bs =>
    match takeField (b :: bs) with
    | some (k, r1) =>
      match takeField r1 with
      | some (v, r2) => (parseEntries f r2).map ((k, v) :: ·)
      | none => none
    | none => none

/-- A string fits a field: fewer than 65536 bytes. -/
def fieldOk (s : String) : Bool := decide ((strBytes s).length < 65536)

theorem takeField_field {s : String} (h : fieldOk s = true) (rest : List UInt8) :
    takeField (field s ++ rest) = some (s, rest) := by
  simp only [fieldOk, decide_eq_true_eq] at h
  simp only [field, u16, List.cons_append, List.nil_append, takeField]
  rw [toNat_ofNat_lt (by omega), toNat_ofNat_lt (by omega)]
  rw [show (strBytes s).length / 256 * 256 + (strBytes s).length % 256 = (strBytes s).length by omega]
  simp [strOfBytes_strBytes]

theorem takeField_eq {bs rest : List UInt8} {s : String} (h : takeField bs = some (s, rest)) :
    fieldOk s = true ∧ bs = field s ++ rest := by
  match bs, h with
  | hi :: lo :: r, h =>
    simp only [takeField] at h
    split at h
    · rename_i hn
      simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
      obtain ⟨s', hs, rfl, rfl⟩ := h
      have hb := strBytes_strOfBytes hs
      have hl : (strBytes s').length = hi.toNat * 256 + lo.toNat := by rw [hb]; simp; omega
      have hh := UInt8.toNat_lt hi; have hlo := UInt8.toNat_lt lo
      refine ⟨by simp [fieldOk, hl]; omega, ?_⟩
      have e1 : UInt8.ofNat ((strBytes s').length / 256) = hi := uint8_eq (by rw [hl]; omega)
      have e2 : UInt8.ofNat ((strBytes s').length % 256) = lo := uint8_eq (by rw [hl]; omega)
      rw [field, u16, e1, e2, hb]
      simp
    · cases h

theorem entries_length (m : MetaValue) : m.length ≤ (entries m).length := by
  induction m with
  | nil => simp
  | cons kv m ih => obtain ⟨k, v⟩ := kv; simp [entries, field, u16]; omega

theorem parseEntries_entries {m : MetaValue} (h : m.all (fun kv => fieldOk kv.1 && fieldOk kv.2) = true)
    {f : Nat} (hf : m.length ≤ f) : parseEntries f (entries m) = some m := by
  induction m generalizing f with
  | nil => cases f <;> rfl
  | cons kv m ih =>
    obtain ⟨k, v⟩ := kv
    simp only [List.all_cons, Bool.and_eq_true] at h
    obtain ⟨⟨hk, hv⟩, h⟩ := h
    obtain ⟨f, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by simp at hf; omega⟩
    obtain ⟨b, bs, hb⟩ : ∃ b bs, entries ((k, v) :: m) = b :: bs := ⟨_, _, rfl⟩
    rw [hb]
    simp only [parseEntries]
    rw [← hb, entries, List.append_assoc, takeField_field hk]
    dsimp only
    rw [takeField_field hv]
    dsimp only
    rw [ih h (by simp at hf; omega)]
    rfl

theorem entries_parseEntries {f : Nat} {bs : List UInt8} {m : MetaValue} (h : parseEntries f bs = some m) :
    m.all (fun kv => fieldOk kv.1 && fieldOk kv.2) = true ∧ entries m = bs := by
  induction f generalizing bs m with
  | zero => match bs, h with | [], h => cases h; simp [entries]
  | succ f ih =>
    match bs, h with
    | [], h => cases h; simp [entries]
    | b :: bs, h =>
      simp only [parseEntries] at h
      split at h
      · rename_i k r1 h1
        split at h
        · rename_i v r2 h2
          simp only [Option.map_eq_some_iff] at h
          obtain ⟨m', hm, rfl⟩ := h
          obtain ⟨hk, e1⟩ := takeField_eq h1; obtain ⟨hv, e2⟩ := takeField_eq h2
          obtain ⟨hw, e3⟩ := ih hm
          simp [entries, hk, hv, hw, e1, e2, e3]
        · cases h
      · cases h

/-! ## Well-formed values, the encoding and the decoding -/

/-- A key: 1 to 64 characters of `a`–`z`, `0`–`9`, `_`. -/
def keyChar (c : Char) : Bool := ('a' ≤ c && c ≤ 'z') || ('0' ≤ c && c ≤ '9') || c == '_'

def validKey (k : String) : Bool := !k.toList.isEmpty && decide (k.toList.length ≤ 64) && k.toList.all keyChar

/-- Keys strictly ascending (so distinct, and one written form per map). -/
def ascending : MetaValue → Bool
  | a :: b :: rest => decide (a.1 < b.1) && ascending (b :: rest)
  | _ => true

/-- **A well-formed value**: valid keys, strictly ascending, each key and value fitting its two-byte length. -/
def MetaValue.wf (m : MetaValue) : Bool :=
  m.all (fun kv => validKey kv.1) && ascending m && m.all (fun kv => fieldOk kv.1 && fieldOk kv.2)

/-- The largest payload whose encoding is a legal core meta: `5 + ⌈4n/3⌉ ≤ 4096` iff `n ≤ 3068`. -/
def maxPayload : Nat := 3068

/-- **It fits**: its payload is at most `maxPayload` bytes. -/
def MetaValue.fits (m : MetaValue) : Bool := decide ((payload m).length ≤ maxPayload)

/-- **The encoding**: `ewm1.` and the payload's base64url. -/
def encode (m : MetaValue) : String := String.ofList ('e' :: 'w' :: 'm' :: '1' :: '.' :: b64enc (payload m))

/-- **The decoding**: `some` exactly the well-formed values that fit, read from their encoding. -/
def decode (s : String) : Option MetaValue :=
  match s.toList with
  | 'e' :: 'w' :: 'm' :: '1' :: '.' :: body =>
    match b64dec body with
    | some (v :: bs) =>
      if v = version then
        match parseEntries bs.length bs with
        | some m => if m.wf && m.fits then some m else none
        | none => none
      else none
    | _ => none
  | _ => none

/-- A `meta` field, decoded: absent decodes to nothing. -/
def decodeMeta : Meta → Option MetaValue
  | none => none
  | some s => decode s

theorem wf_fields {m : MetaValue} (h : m.wf = true) : m.all (fun kv => fieldOk kv.1 && fieldOk kv.2) = true := by
  simp only [MetaValue.wf, Bool.and_eq_true] at h; exact h.2

/-- **Round trip**: a well-formed value that fits decodes from its encoding. -/
theorem decode_encode {m : MetaValue} (hw : m.wf = true) (hf : m.fits = true) : decode (encode m) = some m := by
  simp only [decode, encode, String.toList_ofList, payload, b64dec_enc, ↓reduceIte]
  rw [parseEntries_entries (wf_fields hw) (entries_length m)]
  simp [hw, hf]

/-- **Whatever decodes is well formed and fits.** -/
theorem decode_wf {s : String} {m : MetaValue} (h : decode s = some m) : m.wf = true ∧ m.fits = true := by
  simp only [decode] at h
  split at h
  · split at h
    · split at h
      · split at h
        · split at h
          · cases h; simp_all
          · cases h
        · cases h
      · cases h
    · cases h
  · cases h

/-- **Canonical**: whatever decodes is encoded back to exactly the string it came from. -/
theorem encode_decode {s : String} {m : MetaValue} (h : decode s = some m) : encode m = s := by
  simp only [decode] at h
  split at h
  · rename_i body hs
    split at h
    · rename_i v bs hb
      split at h
      · rename_i hv
        split at h
        · rename_i m' hm
          split at h
          · cases h
            have he := (entries_parseEntries hm).2
            have hb' := b64enc_dec hb
            rw [← String.ofList_toList (s := s), hs, encode, payload, he, ← hv, hb']
          · cases h
        · cases h
      · cases h
    · cases h
  · cases h

/-- **`decode` is injective**: two strings that decode to the same value are the same string. -/
theorem decode_inj {s₁ s₂ : String} {m : MetaValue} (h₁ : decode s₁ = some m) (h₂ : decode s₂ = some m) :
    s₁ = s₂ := by
  rw [← encode_decode h₁, ← encode_decode h₂]

/-- **`encode` is injective** on the values that decode. -/
theorem encode_inj {m₁ m₂ : MetaValue} (hw₁ : m₁.wf = true) (hf₁ : m₁.fits = true) (hw₂ : m₂.wf = true)
    (hf₂ : m₂.fits = true) (h : encode m₁ = encode m₂) : m₁ = m₂ := by
  have := decode_encode hw₁ hf₁; rw [h, decode_encode hw₂ hf₂] at this; exact Option.some.inj this.symm

/-- **`encode` is the only preimage**: `decode s = some m` iff `s` is `m`'s encoding and `m` is well formed and fits. -/
theorem decode_eq_some_iff {s : String} {m : MetaValue} :
    decode s = some m ↔ m.wf = true ∧ m.fits = true ∧ encode m = s := by
  constructor
  · intro h; exact ⟨(decode_wf h).1, (decode_wf h).2, encode_decode h⟩
  · rintro ⟨hw, hf, rfl⟩; exact decode_encode hw hf

/-! ## Every structured meta is a legal core meta -/

theorem sextetChar_utf8Size : ∀ i : Fin 64, (sextetChar i).utf8Size = 1 := by decide
theorem sextetChar_b64 : ∀ i : Fin 64,
    ((sextetChar i).isAlphanum || sextetChar i == '-' || sextetChar i == '_') = true := by decide
theorem sextetChar_ne_eq : ∀ i : Fin 64, (sextetChar i == '=') = false := by decide
theorem sextetChar_ne_nul : ∀ i : Fin 64, (sextetChar i == '\x00') = false := by decide

theorem utf8Encode_size (l : List Char) : l.utf8Encode.size = (l.map Char.utf8Size).sum := by
  induction l with
  | nil => simp
  | cons c l ih =>
    rw [List.utf8Encode_cons, ByteArray.size_append, ih, List.utf8Encode_singleton, List.size_toByteArray,
      String.length_utf8EncodeChar]
    simp

theorem b64enc_utf8 (l : List UInt8) : ((b64enc l).map Char.utf8Size).sum = (b64enc l).length := by
  suffices ∀ cs : List Char, (∀ c ∈ cs, c.utf8Size = 1) → (cs.map Char.utf8Size).sum = cs.length from
    this _ fun c hc => by obtain ⟨i, hi, rfl⟩ := b64enc_mem hc; exact sextetChar_utf8Size ⟨i, hi⟩
  intro cs h
  induction cs with
  | nil => rfl
  | cons c cs ih => simp [h c (List.mem_cons_self ..), ih fun x hx => h x (List.mem_cons_of_mem _ hx)]; omega

/-- **The size of an encoding**: `5 + ⌈4n/3⌉` bytes, `n` the payload's length. -/
theorem encode_size (m : MetaValue) :
    (encode m).utf8ByteSize = 5 + (4 * (payload m).length + 2) / 3 := by
  rw [← String.size_toByteArray, encode, String.toByteArray_ofList, utf8Encode_size]
  simp only [List.map_cons, List.sum_cons, b64enc_utf8, b64enc_length]
  rw [show ('e').utf8Size = 1 by decide, show ('w').utf8Size = 1 by decide, show ('m').utf8Size = 1 by decide,
    show ('1').utf8Size = 1 by decide, show ('.').utf8Size = 1 by decide]
  omega

/-- The core's `validMeta`, as its docstring states it: `ewm1.`, then base64url (at least one character, then at most
two `=`), at most 4096 bytes. By `rfl`: the interface prints `validMeta` as a signature. -/
def metaForm (s : String) : Bool :=
  let body := (s.drop 5).copy
  let core := (body.toList.reverse.dropWhile (· == '=')).reverse
  s.utf8ByteSize ≤ 4096 && "ewm1.".toList.isPrefixOf s.toList && body.length - core.length ≤ 2 && 1 ≤ core.length &&
    core.all fun c => c.isAlphanum || c == '-' || c == '_'

theorem validMeta_eq : validMeta = metaForm := rfl

/-- The core's `wfMeta` on a present meta: no U+0000, and `validMeta`. By `rfl`, as `validMeta_eq`. -/
theorem wfMeta_some (s : String) : wfMeta (some s) = (!s.any (· == '\x00') && validMeta s) := rfl

theorem dropWhile_none {l : List Char} (h : ∀ c ∈ l, (c == '=') = false) : l.dropWhile (· == '=') = l := by
  cases l with
  | nil => rfl
  | cons c l => simp [h c (List.mem_cons_self ..)]

theorem payload_length_pos (m : MetaValue) : 0 < (payload m).length := by simp [payload]

/-- **Exactly when an encoding is a legal core meta**: when its payload is at most 3068 bytes. -/
theorem validMeta_encode_iff (m : MetaValue) : validMeta (encode m) = true ↔ (payload m).length ≤ maxPayload := by
  rw [validMeta_eq]
  have hmem : ∀ c ∈ b64enc (payload m), ∃ i < 64, sextetChar i = c := fun _ h => b64enc_mem h
  have hne : ∀ c ∈ (b64enc (payload m)).reverse, (c == '=') = false := fun c hc => by
    obtain ⟨i, hi, rfl⟩ := hmem c (List.mem_reverse.mp hc); exact sextetChar_ne_eq ⟨i, hi⟩
  have hlen := b64enc_length (payload m)
  have hpos := payload_length_pos m
  have hs := encode_size m
  simp only [metaForm]
  rw [hs, ← String.length_toList, String.toList_copy_drop]
  simp only [encode, String.toList_ofList, List.drop_succ_cons, List.drop_zero, dropWhile_none hne,
    List.reverse_reverse]
  have hall : (b64enc (payload m)).all (fun c => c.isAlphanum || c == '-' || c == '_') = true := by
    rw [List.all_eq_true]; intro c hc; obtain ⟨i, hi, rfl⟩ := hmem c hc; exact sextetChar_b64 ⟨i, hi⟩
  have hp : "ewm1.".toList = ['e', 'w', 'm', '1', '.'] := rfl
  simp only [hall, hp, List.isPrefixOf, Bool.and_true, beq_self_eq_true, Nat.sub_self, Bool.and_eq_true,
    decide_eq_true_eq, maxPayload, hlen]
  omega

/-- **Every structured meta that fits is a legal core meta** (`wfMeta`): the form the core checks when it parses one. -/
theorem wfMeta_encode {m : MetaValue} (hf : m.fits = true) : wfMeta (some (encode m)) = true := by
  rw [wfMeta_some]
  simp only [MetaValue.fits, decide_eq_true_eq] at hf
  have hnul : (encode m).any (· == '\x00') = false := by
    show (encode m).contains (· == '\x00') = false
    rw [String.contains_bool_eq, encode, String.toList_ofList]
    have hb : (b64enc (payload m)).any (· == '\x00') = false := by
      rw [List.any_eq_false]; intro c hc
      obtain ⟨i, hi, rfl⟩ := b64enc_mem hc; simpa using sextetChar_ne_nul ⟨i, hi⟩
    simp only [List.any_cons, hb]
    decide
  simp [hnul, (validMeta_encode_iff m).mpr hf]

/-- **Whatever decodes is a legal core meta.** -/
theorem decode_wfMeta {s : String} {m : MetaValue} (h : decode s = some m) : wfMeta (some s) = true := by
  rw [← encode_decode h]; exact wfMeta_encode (decode_wf h).2

/-! ## Meta on events: the core's six, and any service's command/event bijection -/

/-- The meta of a core event. -/
def eventMeta : Event → Meta
  | .streamCreate _ _ _ m | .principalInvite _ _ _ m | .principalPromote _ _ _ m | .principalDemote _ _ _ m
  | .principalBan _ _ _ m | .streamPanic _ _ m => m

/-- The meta of a core command. -/
def commandMeta : Command → Meta
  | .streamCreate _ m | .principalInvite _ _ m | .principalPromote _ _ m | .principalDemote _ _ m
  | .principalBan _ _ m | .streamPanic _ m => m

/-- **An event's meta is its command's**, for any service whose request of an event carries the event's meta (`hreq`:
on a concrete layer, by cases and `rfl`): the request that makes an event is that event's request (the service's
bijection, `toEvent_ok_iff`), so it carries exactly the event's meta, and the event's structured meta is the
command's. -/
theorem toEvent_meta_of {S : Service} (evMeta : S.Ev → Meta) (reqMeta : S.Req → Meta)
    (hreq : ∀ e, reqMeta (S.toRequest e) = evMeta e) {r : S.Req} {e : S.Ev} (h : S.toEvent r = .ok e) :
    evMeta e = reqMeta r := by
  rw [← S.toEvent_ok_iff.mp h, hreq]

/-! ## Schemas -/

/-- The kind of a field's value. -/
inductive FieldKind where
  /-- Any non-empty string. -/
  | text
  /-- A canonical lowercase UUID (the core's `validUuid`). -/
  | uuid
  /-- A string your predicate accepts (a URL: `url_kind`'s `validUrlWith`). -/
  | str (wf : String → Bool)

def FieldKind.ok : FieldKind → String → Bool
  | .text, s => !s.isEmpty
  | .uuid, s => validUuid s
  | .str wf, s => wf s

/-- One field of a schema: its key, its kind, and whether it is required. -/
structure FieldSpec where
  key : String
  kind : FieldKind
  required : Bool

abbrev Schema := List FieldSpec

/-- A field's value, if present. -/
def MetaValue.get (m : MetaValue) (k : String) : Option String := m.lookup k

/-- Every required key of the schema present. -/
def hasRequired (sc : Schema) (m : MetaValue) : Bool := sc.all fun f => !f.required || (m.get f.key).isSome

/-- Every key of the value in the schema, its value of that field's kind. -/
def fieldsOk (sc : Schema) (m : MetaValue) : Bool :=
  m.all fun (k, v) => match sc.find? (·.key == k) with
    | some f => f.kind.ok v
    | none => false

/-- **The value conforms to the schema.** -/
def conforms (sc : Schema) (m : MetaValue) : Bool := hasRequired sc m && fieldsOk sc m

/-- A required field of a conforming value is present. -/
theorem conforms_required {sc : Schema} {m : MetaValue} (h : conforms sc m = true) {f : FieldSpec}
    (hf : f ∈ sc) (hr : f.required = true) : ∃ v, m.get f.key = some v := by
  simp only [conforms, hasRequired, Bool.and_eq_true, List.all_eq_true] at h
  have := h.1 f hf
  simp [hr] at this
  exact Option.isSome_iff_exists.mp this

theorem lookup_mem {m : MetaValue} {k v : String} (h : m.lookup k = some v) : (k, v) ∈ m := by
  induction m with
  | nil => simp at h
  | cons kv m ih =>
    obtain ⟨k', v'⟩ := kv
    by_cases hk : k = k'
    · subst hk; simp [List.lookup] at h; subst h; exact List.mem_cons_self ..
    · simp [List.lookup, show (k == k') = false by simpa using hk] at h; exact List.mem_cons_of_mem _ (ih h)

/-- A present field of a conforming value is of its schema's kind. -/
theorem conforms_kind {sc : Schema} {m : MetaValue} (h : conforms sc m = true) {k v : String}
    (hv : m.get k = some v) : ∃ f, sc.find? (·.key == k) = some f ∧ f.kind.ok v = true := by
  simp only [conforms, fieldsOk, Bool.and_eq_true, List.all_eq_true] at h
  have := h.2 (k, v) (lookup_mem hv)
  revert this; cases hf : sc.find? (·.key == k) with
  | none => simp
  | some f => intro hk; exact ⟨f, rfl, hk⟩

/-! ## Rules that read meta: the triple a layer's rules use, and what they say together -/

/-- The meta decodes (a structured meta at all): the rule `meta_invalid`. -/
def metaOk (m : Meta) : Bool := (decodeMeta m).isSome

/-- The decoded meta has every field the schema requires (vacuous when it does not decode: `meta_invalid` first): the
rule `meta_missing_field`. -/
def metaRequired (sc : Schema) (m : Meta) : Bool := match decodeMeta m with
  | some v => hasRequired sc v
  | none => true

/-- Every field of the decoded meta is in the schema and of its kind (vacuous when it does not decode): the rule
`meta_bad_field`. -/
def metaFields (sc : Schema) (m : Meta) : Bool := match decodeMeta m with
  | some v => fieldsOk sc v
  | none => true

/-- **The three rules together**: the meta decodes, to a value that conforms to the schema. With the rules found by
name (`holdsNamed`), `(meta_rules_iff sc m).mp (by simp_all)` gives the decoded value; in an `*_ok_iff`, `rw
[h.snoc_inr_iff, ← meta_rules_iff]` then `simp`. -/
theorem meta_rules_iff (sc : Schema) (m : Meta) :
    (metaOk m && metaRequired sc m && metaFields sc m) = true ↔ ∃ v, decodeMeta m = some v ∧ conforms sc v = true := by
  cases hd : decodeMeta m <;> simp [metaOk, metaRequired, metaFields, hd, conforms]

/-! ### Using it: a value, its encoding, and back -/

def example1 : MetaValue := [("link", "https://example.org/a"), ("title", "Hello, wörld")]

#guard example1.wf && example1.fits
#guard decode (encode example1) == some example1
#guard (encode example1).startsWith "ewm1.AQ"
#guard wfMeta (some (encode example1))
#guard decode "ewm1.aGk" == none
#guard decode (encode [("title", "x"), ("link", "y")]) == none
#guard conforms [⟨"title", .text, true⟩, ⟨"link", .str (·.startsWith "https://"), false⟩] example1
#guard !conforms [⟨"title", .text, true⟩] example1
#guard metaOk (some (encode example1)) && !metaOk (some "ewm1.aGk") && !metaRequired [⟨"color", .text, true⟩] (some (encode example1))

end Work
