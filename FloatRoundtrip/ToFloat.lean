/-!
# Reading a float back

`String.Slice.toFloat?` from matthiasgoergens/lean4#9 (2a99bba6eb), copied with `private` dropped
so that the proofs can refer to its helpers, and moved into namespace `FloatRoundtrip`.
-/

namespace FloatRoundtrip

open String

/-- Splits `s` at the first character satisfying `p`, without that character. -/
def splitAtFirst? (s : String.Slice) (p : Char → Bool) : Option (Slice × Slice) :=
  (s.find? p).map fun pos => (s.sliceTo pos, (s.sliceFrom pos).drop 1)

/--
The value and the number of digits of a possibly empty run of decimal digits, with `_` allowed
between digits as in `String.Slice.toNat?`, or `none` if it is not such a run.
-/
def digitRun? (s : String.Slice) : Option (Nat × Nat) :=
  if s.isEmpty then some (0, 0)
  else if s.isNat then
    some (s.foldl (fun n c => if c = '_' then n else n * 10 + (c.toNat - '0'.toNat)) 0,
      s.foldl (fun k c => if c = '_' then k else k + 1) 0)
  else none

/--
Splits a decimal number with an optional `-`, fraction and exponent into
`(negative, mantissa, exponent)`, with the value `±mantissa * 10 ^ exponent`.
-/
def decimalParts? (s : String.Slice) : Option (Bool × Nat × Int) := do
  let (negative, s) := match s.dropPrefix? '-' with
    | some rest => (true, rest)
    | none => (false, s)
  let (mantissa, exponent) ← match splitAtFirst? s (fun c => c = 'e' || c = 'E') with
    | some (mantissa, exp) =>
      let (expNegative, exp) := match exp.dropPrefix? '-', exp.dropPrefix? '+' with
        | some rest, _ => (true, rest)
        | none, some rest => (false, rest)
        | none, none => (false, exp)
      exp.toNat?.map fun e => (mantissa, if expNegative then -(e : Int) else e)
    | none => some (s, 0)
  let (intPart, fracPart) := match splitAtFirst? mantissa (· = '.') with
    | some parts => parts
    | none => (mantissa, mantissa.sliceFrom mantissa.endPos)
  let (i, intDigits) ← digitRun? intPart
  let (f, fracDigits) ← digitRun? fracPart
  guard (intDigits + fracDigits > 0)
  return (negative, i * 10 ^ fracDigits + f, exponent - fracDigits)

/--
Interprets a slice as a floating-point number, returning the nearest `Float` (ties to even),
or `none` if the slice is not a number.

Accepted are an optional `-`, decimal digits with an optional fraction after `.`, and an
optional exponent after `e` or `E` with an optional sign, as well as `inf`,
`-inf` and `NaN`. Underscores (`_`) are allowed between digits. This reads back
what `Float.toString` writes.

Examples:
 * `"0.1".toSlice.toFloat? = some 0.1`
 * `"-1.5e-3".toSlice.toFloat? = some (-0.0015)`
 * `"1e400".toSlice.toFloat? = some Float.inf`
 * `"1_000.5".toSlice.toFloat? = some 1000.5`
 * `".5".toSlice.toFloat? = some 0.5`
 * `"0x10".toSlice.toFloat? = none`
-/
def toFloat? (s : String.Slice) : Option Float :=
  if s == "inf".toSlice then some Float.inf
  else if s == "-inf".toSlice then some (-Float.inf)
  else if s == "NaN".toSlice then some Float.nan
  else
    (decimalParts? s).map fun (negative, m, e) =>
      let x : Float := OfScientific.ofScientific m (e < 0) e.natAbs
      if negative then -x else x

end FloatRoundtrip
