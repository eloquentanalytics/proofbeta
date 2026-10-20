-- Copyright (c) 2026 the proofbeta authors. All rights reserved. See LICENSE.
import StreamCore.WireTheorems
import StreamCore.Oracle

/-!
# Bytes to JSON values and back

Our own JSON parser and printer over `J`, in core Lean: structural recursion, or a fuel argument that the input's
length bounds; no `partial`, no Lean library parser. What of this is not proved is stated in `Theorems.lean`. Both
reproduce, byte for byte where the engine's answers depend on it, what the engine did up to Lean v4.12.0 with
`Lean.Json.parse` and `Lean.Json.compress` (sessions recorded from that engine replay through them); the `#guard`s at the end of this
file check the cases below.

What the parser does, as Lean v4.12.0's did:
- a `\u` escape of a UTF-16 surrogate (U+D800 to U+DFFF, paired or lone) decodes to U+0000, so `Wire.noNul` refuses
  any string holding one (an id cannot hold one: `validUuid` excludes control characters). The host sends UTF-8
  unescaped, so astral characters arrive whole;
- an object's keys come out sorted (by `<` on strings, code point order) and a repeated key keeps its last value. The
  host refuses repeated keys before anything reaches the engine;
- a number becomes `.num n` when it is a natural (no fraction digits left after the exponent, not negative; `-0` is
  `0`), and otherwise `notNatural`;
- whitespace is space, tab, line feed and carriage return; a refused line answers `offset <byte>: <reason>`, with the
  reasons and offsets Lean's parser gave.

What the printer does, as `Lean.Json.compress` did: no whitespace; an object's keys in descending order, a repeated key
printed once with its last value; `"`, `\`, line feed and carriage return escaped as `\"`, `\\`, `\n`, `\r`, any
other character below U+0020 as `\u00xx` (lowercase hex), everything else as itself.

Both conversions stop at a depth budget (`depth`); anything deeper becomes `null`, which no decoder accepts where a
value is required. The protocol's values are at most four levels deep.
-/

namespace StreamCore.Wire

def depth : Nat := 32

/-- What a number that is not a natural becomes: a string holding U+0000, which no decoder accepts anywhere
(`Wire.noNul`, as for an escaped surrogate). No field of the protocol holds such a number; it used to become `null`,
which `meta` accepts, so `meta: -1` decoded as no meta (round 3). -/
def notNatural : J := .str "\x00"

/-! ## Objects: sorted keys, the last value of a repeated key -/

/-- From a list sorted by key (a stable sort, so equal keys keep their input order), the last pair of each key, in
descending key order. -/
def lastOfRuns : (String × J) → List (String × J) → List (String × J) → List (String × J)
  | cur, [], acc => cur :: acc
  | cur, y :: rest, acc => if cur.1 == y.1 then lastOfRuns y rest acc else lastOfRuns y rest (cur :: acc)

/-- An object's pairs as Lean v4.12.0's `RBNode` held them, in descending key order: one pair per key, its last value. -/
def keysDescending (kvs : List (String × J)) : List (String × J) :=
  match kvs.mergeSort (fun a b => !(b.1 < a.1)) with
  | [] => []
  | x :: rest => lastOfRuns x rest []

/-! ## Printing -/

def hexLower (n : Nat) : Char := if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)

def escapeInto (acc : String) (c : Char) : String :=
  if c == '"' then acc ++ "\\\""
  else if c == '\\' then acc ++ "\\\\"
  else if c == '\n' then acc ++ "\\n"
  else if c == '\r' then acc ++ "\\r"
  else if 0x20 ≤ c.val then acc.push c
  else ((acc ++ "\\u00").push (hexLower (c.toNat / 16))).push (hexLower (c.toNat % 16))

def renderStr (acc s : String) : String := (s.toList.foldl escapeInto (acc.push '"')).push '"'

/-- `j` printed after `acc`, with `n` levels left. -/
def renderInto : Nat → J → String → String
  | 0, _, acc => acc ++ "null"
  | _ + 1, .null, acc => acc ++ "null"
  | _ + 1, .bool true, acc => acc ++ "true"
  | _ + 1, .bool false, acc => acc ++ "false"
  | _ + 1, .num k, acc => acc ++ Nat.repr k
  | _ + 1, .str s, acc => renderStr acc s
  | n + 1, .arr xs, acc =>
    (xs.foldl (fun (a, first) x => (renderInto n x (if first then a else a.push ','), false)) (acc.push '[', true)).1.push ']'
  | n + 1, .obj kvs, acc =>
    (keysDescending kvs |>.foldl (fun (a, first) (k, v) =>
      (renderInto n v ((renderStr (if first then a else a.push ',') k).push ':'), false)) (acc.push '{', true)).1.push '}'

/-- A JSON value out, as one line. -/
def render (j : J) : String := renderInto depth j ""

/-! ## Parsing

A parser takes the remaining characters and the byte offset of the first; it answers the value, the rest and its
offset, or the offset and reason of a refusal. -/

abbrev Ex := Except (Nat × String)

abbrev PR (α : Type) := Ex (α × List Char × Nat)

def eoi : String := "unexpected end of input"

/-- Never reached: the fuel (twice the input's length, plus some) outlasts the input, and every call consumes. -/
def outOfFuel : String := "input too deep"

def isWs (c : Char) : Bool := c == ' ' || c == '\t' || c == '\n' || c == '\r'

def isDigit (c : Char) : Bool := '0' ≤ c && c ≤ '9'

def skipWs : List Char → Nat → List Char × Nat
  | c :: cs, p => if isWs c then skipWs cs (p + 1) else (c :: cs, p)
  | [], p => ([], p)

def hexVal (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - 48)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 87)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 55)
  else none

/-- Four hex digits after `\u`: their value, or the refusal. -/
def hex4 (cs : List Char) (p : Nat) : Ex (Nat × List Char × Nat) :=
  let one (acc : Nat) (cs : List Char) (p : Nat) : PR Nat :=
    match cs with
    | [] => .error (p, eoi)
    | c :: r => match hexVal c with
      | some v => .ok (16 * acc + v, r, p + c.utf8Size)
      | none => .error (p + c.utf8Size, "invalid hex character")
  do
    let (a, cs, p) ← one 0 cs p
    let (a, cs, p) ← one a cs p
    let (a, cs, p) ← one a cs p
    one a cs p

/-- A string's characters after its opening quote, up to and past the closing one. `Char.ofNat` of a surrogate is
U+0000. -/
def strBody : Nat → String → List Char → Nat → PR String
  | 0, _, _, p => .error (p, outOfFuel)
  | _ + 1, _, [], p => .error (p, eoi)
  | f + 1, acc, c :: cs, p =>
    if c == '"' then .ok (acc, cs, p + 1)
    else if c == '\\' then
      match cs with
      | [] => .error (p + 1, eoi)
      | e :: r =>
        let q := p + 1 + e.utf8Size
        if e == '\\' then strBody f (acc.push '\\') r q
        else if e == '"' then strBody f (acc.push '"') r q
        else if e == '/' then strBody f (acc.push '/') r q
        else if e == 'b' then strBody f (acc.push '\x08') r q
        else if e == 'f' then strBody f (acc.push '\x0c') r q
        else if e == 'n' then strBody f (acc.push '\n') r q
        else if e == 'r' then strBody f (acc.push '\r') r q
        else if e == 't' then strBody f (acc.push '\t') r q
        else if e == 'u' then
          match hex4 r q with
          | .error x => .error x
          | .ok (v, r, q) => strBody f (acc.push (Char.ofNat v)) r q
        else .error (q, "illegal \\u escape")
    else if 0x20 ≤ c.val then strBody f (acc.push c) cs (p + c.utf8Size)
    else .error (p + c.utf8Size, "unexpected character in string")

/-- Decimal digits: their value, how many, the rest and its offset. -/
def digits (acc k : Nat) : List Char → Nat → Nat × Nat × List Char × Nat
  | c :: cs, p => if isDigit c then digits (10 * acc + (c.toNat - 48)) (k + 1) cs (p + 1) else (acc, k, c :: cs, p)
  | [], p => (acc, k, [], p)

/-- At least one digit (refused with `what` otherwise), then as many as follow. -/
def someDigits (what : String) (cs : List Char) (p : Nat) : Ex ((Nat × Nat) × List Char × Nat) :=
  match cs with
  | [] => .error (p, eoi)
  | c :: _ => if isDigit c then let (v, k, r, q) := digits 0 0 cs p; .ok ((v, k), r, q) else .error (p, what)

/-- As `USize.size` on a 64-bit platform: Lean's parser refused more fraction digits or a larger exponent. -/
def usizeSize : Nat := 18446744073709551616

/-- `m * 10^-e` as `J`. -/
def numberJ (m : Int) (e : Nat) : J := if e == 0 && m ≥ 0 then .num m.toNat else notNatural

/-- A number: `-`?, `0` or a nonzero digit and digits, then `.` and digits?, then `e`/`E`, `+`/`-`? and digits?. -/
def number (cs : List Char) (p : Nat) : Ex (J × List Char × Nat) := do
  let (neg, cs, p) := match cs with | '-' :: r => (true, r, p + 1) | _ => (false, cs, p)
  let sign : Int := if neg then -1 else 1
  let (whole, cs, p) ← match cs with
    | [] => .error (p, eoi)
    | c :: r =>
      if c == '0' then .ok (0, r, p + 1)
      else if '1' ≤ c && c ≤ '9' then let (v, _, r, q) := digits 0 0 cs p; .ok (v, r, q)
      else .error (p, "expected 1-9")
  let ((m, e), cs, p) ← match cs with
    | '.' :: r => do
      let ((n, k), r, q) ← someDigits "expected digit" r (p + 1)
      if k > usizeSize then .error (q, "too many decimals")
      else .ok ((sign * ((whole * 10 ^ k + n : Nat) : Int), k), r, q)
    | _ => .ok ((sign * (whole : Int), 0), cs, p)
  match cs with
  | c :: r =>
    if c == 'e' || c == 'E' then
      match r with
      | [] => .error (p + 1, eoi)
      | '-' :: r => do
        let ((n, _), r, q) ← someDigits "expected 0-9" r (p + 2)
        .ok (numberJ m (e + n), r, q)
      | c2 :: r2 => do
        let (r, q) := if c2 == '+' then (r2, p + 2) else (r, p + 1)
        let ((n, _), r, q) ← someDigits "expected 0-9" r q
        if n > usizeSize then .error (q, "exp too large")
        else .ok (numberJ (m * ((10 ^ (n - e) : Nat) : Int)) (e - n), r, q)
    else .ok (numberJ m e, cs, p)
  | [] => .ok (numberJ m e, [], p)

/-- `true`, `false` or `null`. -/
def word (w : String) (j : J) (cs : List Char) (p : Nat) : PR J :=
  let ws := w.toList
  if ws.isPrefixOf cs then let (r, q) := skipWs (cs.drop ws.length) (p + ws.length); .ok (j, r, q)
  else .error (p, "expected: " ++ w)

mutual

/-- A value, then the whitespace after it. -/
def value : Nat → List Char → Nat → PR J
  | 0, _, p => .error (p, outOfFuel)
  | _ + 1, [], p => .error (p, eoi)
  | f + 1, c :: cs, p =>
    if c == '[' then
      let (cs, p) := skipWs cs (p + 1)
      match cs with
      | [] => .error (p, eoi)
      | c' :: r =>
        if c' == ']' then let (r, q) := skipWs r (p + 1); .ok (.arr [], r, q)
        else arrItems f [] cs p
    else if c == '{' then
      let (cs, p) := skipWs cs (p + 1)
      match cs with
      | [] => .error (p, eoi)
      | c' :: r =>
        if c' == '}' then let (r, q) := skipWs r (p + 1); .ok (.obj [], r, q)
        else objMembers f [] cs p
    else if c == '"' then
      match strBody f "" cs (p + 1) with
      | .error x => .error x
      | .ok (s, r, q) => let (r, q) := skipWs r q; .ok (.str s, r, q)
    else if c == 'f' then word "false" (.bool false) (c :: cs) p
    else if c == 't' then word "true" (.bool true) (c :: cs) p
    else if c == 'n' then word "null" .null (c :: cs) p
    else if c == '-' || isDigit c then
      match number (c :: cs) p with
      | .error x => .error x
      | .ok (j, r, q) => let (r, q) := skipWs r q; .ok (j, r, q)
    else .error (p, "unexpected input")

/-- An array's items, after `[` and the whitespace after it; `acc` holds the items so far, last first. -/
def arrItems : Nat → List J → List Char → Nat → PR J
  | 0, _, _, p => .error (p, outOfFuel)
  | f + 1, acc, cs, p =>
    match value f cs p with
    | .error x => .error x
    | .ok (v, cs, p) =>
      match cs with
      | [] => .error (p, eoi)
      | c :: r =>
        if c == ']' then let (r, q) := skipWs r (p + 1); .ok (.arr (v :: acc).reverse, r, q)
        else if c == ',' then let (r, q) := skipWs r (p + 1); arrItems f (v :: acc) r q
        else .error (p + c.utf8Size, "unexpected character in array")

/-- An object's members, after `{` and the whitespace after it; `acc` holds the pairs so far, last first. -/
def objMembers : Nat → List (String × J) → List Char → Nat → PR J
  | 0, _, _, p => .error (p, outOfFuel)
  | f + 1, acc, cs, p =>
    match cs with
    | [] => .error (p, eoi)
    | c :: r =>
      if c != '"' then .error (p, "expected \"") else
      match strBody f "" r (p + 1) with
      | .error x => .error x
      | .ok (k, r, q) =>
        let (r, q) := skipWs r q
        match r with
        | [] => .error (q, eoi)
        | c :: r' =>
          if c != ':' then .error (q, "expected :") else
          let (r, q) := skipWs r' (q + 1)
          match value f r q with
          | .error x => .error x
          | .ok (v, r, q) =>
            match r with
            | [] => .error (q, eoi)
            | c :: r' =>
              if c == '}' then
                let (r, q) := skipWs r' (q + 1)
                let kvs := ((k, v) :: acc).reverse
                .ok (.obj (keysDescending kvs).reverse, r, q)
              else if c == ',' then let (r, q) := skipWs r' (q + 1); objMembers f ((k, v) :: acc) r q
              else .error (q + c.utf8Size, "unexpected character in object")

end

/-- The depth budget: what is deeper than `n` levels becomes `null`. -/
def cut : Nat → J → J
  | 0, _ => .null
  | n + 1, .arr xs => .arr (xs.map (cut n))
  | n + 1, .obj kvs => .obj (kvs.map fun (k, v) => (k, cut n v))
  | _ + 1, j => j

/-- A line in, a JSON value out (or the parser's complaint). -/
def parseLine (line : String) : Except String J :=
  let (cs, p) := skipWs line.toList 0
  match value (2 * cs.length + 8) cs p with
  | .error (q, why) => .error s!"offset {q}: {why}"
  | .ok (j, [], _) => .ok (cut depth j)
  | .ok (_, _ :: _, q) => .error s!"offset {q}: expected end of input"

/-! ## Bytes round trips, checked at build time (tested, not proved) -/

deriving instance BEq for J

def sampleUrl := "https://git.example.org/ädmin-é-😀/repo/commit/0123456789abcdef0123456789abcdef01234567"

def sampleRequests : List Request :=
  [ (Examples.alice, .streamCreate sampleUrl (some "ewm1.aGk="), [Examples.stream]),
    (Examples.alice, .principalInvite Examples.stream Examples.bob none, []),
    (Examples.alice, .principalPromote Examples.stream Examples.bob none, []),
    (Examples.bob, .principalDemote Examples.stream Examples.alice (some "ewm1.x"), []),
    (Examples.bob, .principalBan Examples.stream Examples.alice none, []),
    (Examples.bob, .streamPanic Examples.stream (some "ewm1.x"), []) ]

def roundTripRequest (r : Request) : Bool :=
  match parseLine (render (requestToJ r)) >>= requestFromJ with
  | .ok r' => r' == r
  | .error _ => false

def roundTripEvent (e : Event) : Bool :=
  match parseLine (render (eventToJ e)) >>= eventFromJ with
  | .ok e' => e' == e
  | .error _ => false

def eventsRoundTrip : Bool :=
  sampleRequests.all fun r => match toEvent r.1 r.2.1 r.2.2 with | .ok e => roundTripEvent e | _ => false

def refuses (line : String) : Bool :=
  match parseLine line >>= requestFromJ with
  | .ok _ => false
  | .error _ => true

/-- Lines the decoder must refuse: an escaped surrogate pair, a caller-supplied actor, an id with a space, an
uppercase id, a bad meta, an unknown command, a missing field, an id that is not a UUID, a missing `fresh`. -/
def badLines : List String :=
  [ "{\"caller\":{\"principal\":\"a11ce000-0000-4000-8000-000000000001\"},\"command\":{\"command\":\"stream.panic\",\"stream\":\"\\ud83d\\ude00\"},\"fresh\":[]}",
    "{\"caller\":{\"principal\":\"a11ce000-0000-4000-8000-000000000001\"},\"command\":{\"command\":\"stream.panic\",\"stream\":\"7ea30000-0000-7000-8000-000000000001\",\"actor\":\"b0b00000-0000-4000-8000-000000000002\"},\"fresh\":[]}",
    "{\"caller\":{\"principal\":\"a11ce000-0000-4000-8000-000000000001 \"},\"command\":{\"command\":\"stream.panic\",\"stream\":\"7ea30000-0000-7000-8000-000000000001\"},\"fresh\":[]}",
    "{\"caller\":{\"principal\":\"A11CE000-0000-4000-8000-000000000001\"},\"command\":{\"command\":\"stream.panic\",\"stream\":\"7ea30000-0000-7000-8000-000000000001\"},\"fresh\":[]}",
    "{\"caller\":{\"principal\":\"a11ce000-0000-4000-8000-000000000001\"},\"command\":{\"command\":\"stream.panic\",\"stream\":\"7ea30000-0000-7000-8000-000000000001\",\"meta\":\"nope\"},\"fresh\":[]}",
    "{\"caller\":{\"principal\":\"a11ce000-0000-4000-8000-000000000001\"},\"command\":{\"command\":\"stream.drop\",\"stream\":\"7ea30000-0000-7000-8000-000000000001\"},\"fresh\":[]}",
    "{\"caller\":{\"principal\":\"a11ce000-0000-4000-8000-000000000001\"},\"command\":{\"command\":\"principal.promote\",\"stream\":\"7ea30000-0000-7000-8000-000000000001\"},\"fresh\":[]}",
    "{\"caller\":{\"principal\":\"a11ce000-0000-4000-8000-000000000001\"},\"command\":{\"command\":\"principal.invite\",\"stream\":\"7ea30000-0000-7000-8000-000000000001\",\"principal\":\"bob\"},\"fresh\":[]}",
    "{\"caller\":{\"principal\":\"a11ce000-0000-4000-8000-000000000001\"},\"command\":{\"command\":\"stream.panic\",\"stream\":\"7ea30000-0000-7000-8000-000000000001\"}}" ]

#guard sampleRequests.all roundTripRequest
#guard eventsRoundTrip
#guard badLines.all refuses
/-- Round 3: `meta: -1` was decoded as no meta. A number that is not a natural is refused wherever it is. -/
def badNumbersRefused : Bool :=
  ["-1", "1.5", "-0.0", "1e-5", "10.0"].all fun n => refuses
    ("{\"caller\":{\"principal\":\"a11ce000-0000-4000-8000-000000000001\"},\"command\":{\"command\":\"stream.panic\"," ++
     "\"stream\":\"7ea30000-0000-7000-8000-000000000001\",\"meta\":" ++ n ++ "},\"fresh\":[]}")

/-- Objects decode with their keys sorted and print them in descending order, as Lean v4.12.0 did. -/
def objectsKeepOrder : Bool :=
  let line := "{\"b\":1,\"a\":[2,{\"c\":3}],\"d\":null}"
  match parseLine line with
  | .ok (.obj kvs) => kvs.map Prod.fst == ["a", "b", "d"] && render (.obj kvs) == "{\"d\":null,\"b\":1,\"a\":[2,{\"c\":3}]}"
  | _ => false

def parsesTo (line : String) (j : J) : Bool :=
  match parseLine line with
  | .ok j' => j' == j
  | .error _ => false

def refusedWith (line why : String) : Bool :=
  match parseLine line with
  | .ok _ => false
  | .error d => d == why

/-- Key order on output: descending, whatever order the pairs are in; a repeated key printed once, its last value. -/
def keyOrder : Bool :=
  render (.obj [("stream", .str "s"), ("at", .num 0), ("accept", .bool true), ("event", .null)]) ==
    "{\"stream\":\"s\",\"event\":null,\"at\":0,\"accept\":true}" &&
  render (.obj [("a", .num 1), ("b", .num 2), ("a", .num 3)]) == "{\"b\":2,\"a\":3}"

/-- Any escaped surrogate, paired or lone, decodes to U+0000 (and `noNul` refuses it). -/
def surrogates : Bool :=
  parsesTo "\"\\ud83d\\ude00\"" (.str "\x00\x00") && parsesTo "\"a\\uDFFFb\"" (.str "a\x00b") &&
  parsesTo "\"\\ud800\"" (.str "\x00") && parsesTo "\"\\u00e9\\uFFFD\"" (.str "é\uFFFD") &&
  parsesTo "\"😀\"" (.str "😀")

/-- A repeated key keeps its last value; the keys come out sorted. -/
def duplicateKeys : Bool :=
  parsesTo "{\"k\":1,\"a\":2,\"k\":3}" (.obj [("a", .num 2), ("k", .num 3)])

/-- Deeper than `depth` levels becomes `null`, on the way in and on the way out. -/
def nesting : Bool :=
  let deep (n : Nat) (inner : String) : String := String.ofList (List.replicate n '[') ++ inner ++ String.ofList (List.replicate n ']')
  let deepJ (n : Nat) (inner : J) : J := (List.range n).foldl (fun j _ => .arr [j]) inner
  parsesTo (deep 31 "7") (deepJ 31 (.num 7)) && parsesTo (deep 32 "7") (deepJ 32 .null) &&
  parsesTo (deep 40 "7") (deepJ 32 .null) && render (deepJ 31 (.num 7)) == deep 31 "7" &&
  render (deepJ 32 (.num 7)) == deep 32 "null" && parsesTo (deep 3000 "") (deepJ 32 .null) && refusedWith (deep 3000 ",") "offset 3000: unexpected input"

/-- Escapes in and out. -/
def escapes : Bool :=
  parsesTo "\"\\\"\\\\\\/\\b\\f\\n\\r\\t\\u0041\"" (.str "\"\\/\x08\x0c\n\r\tA") &&
  render (.str "\"\\/\x08\x0c\n\r\t\x00\x1f\x7fé😀") == "\"\\\"\\\\/\\u0008\\u000c\\n\\r\\u0009\\u0000\\u001f\x7fé😀\"" &&
  refusedWith "\"\\x\"" "offset 3: illegal \\u escape" && refusedWith "\"\\u12g4\"" "offset 6: invalid hex character" &&
  refusedWith "\"a\tb\"" "offset 3: unexpected character in string" && refusedWith "\"ab" "offset 3: unexpected end of input"

/-- Numbers: naturals stay, anything else is `notNatural`; refusals with Lean's offsets and reasons. -/
def numbers : Bool :=
  parsesTo "0" (.num 0) && parsesTo "-0" (.num 0) && parsesTo "12" (.num 12) && parsesTo "1e2" (.num 100) &&
  parsesTo "1.5e1" (.num 15) && parsesTo "1E+1" (.num 10) && parsesTo "1e-0" (.num 1) && parsesTo "-1" notNatural &&
  parsesTo "1.0" notNatural && parsesTo "1e-1" notNatural && parsesTo "[1, 2 ,3 ]" (.arr [.num 1, .num 2, .num 3]) &&
  refusedWith "01" "offset 1: expected end of input" && refusedWith "-a" "offset 1: expected 1-9" &&
  refusedWith "1." "offset 2: unexpected end of input" && refusedWith "1.x" "offset 2: expected digit" &&
  refusedWith "1e" "offset 2: unexpected end of input" && refusedWith "1ex" "offset 2: expected 0-9"

/-- Other refusals, with Lean's offsets and reasons. -/
def refusals : Bool :=
  refusedWith "x" "offset 0: unexpected input" && refusedWith " {} x" "offset 4: expected end of input" &&
  refusedWith "fals" "offset 0: expected: false" && refusedWith "nul" "offset 0: expected: null" &&
  refusedWith "[1;" "offset 3: unexpected character in array" && refusedWith "{\"a\":1;" "offset 7: unexpected character in object" &&
  refusedWith "{a" "offset 1: expected \"" && refusedWith "{\"a\" 1" "offset 5: expected :" &&
  refusedWith "[" "offset 1: unexpected end of input" && refusedWith "[1," "offset 3: unexpected end of input" &&
  refusedWith "{\"é\":x}" "offset 6: unexpected input"

#guard badNumbersRefused
#guard objectsKeepOrder
#guard keyOrder
#guard surrogates
#guard duplicateKeys
#guard nesting
#guard escapes
#guard numbers
#guard refusals

end StreamCore.Wire
