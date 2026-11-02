/-!
# The printer

The shortest decimal that reads back to the same float, laid out as Python's `repr` does.  These
definitions are copied unchanged from matthiasgoergens/lean4#10 (17dbc686da), which makes them the
logical model of `Float.toString`; only the namespace differs.  The model they build on,
`Float.Model`, is the same in Lean v4.36.0-rc2 as at that PR's base.
-/

open Float.Model Float.Model.UnpackedFloat

namespace FloatRoundtrip

/-- `⌊m * 2 ^ e * 10 ^ k⌋`. -/
def scaleFloor (m : Nat) (e k : Int) : Nat :=
  let (num, den) := if 0 ≤ e then (m * 2 ^ e.toNat, 1) else (m, 2 ^ (-e).toNat)
  if 0 ≤ k then num * 10 ^ k.toNat / den else num / (den * 10 ^ (-k).toNat)

/-- Whether `m * 2 ^ e ≥ 10 ^ k`. -/
def atLeastPowerOfTen (m : Nat) (e k : Int) : Bool :=
  let (num, den) := if 0 ≤ e then (m * 2 ^ e.toNat, 1) else (m, 2 ^ (-e).toNat)
  if 0 ≤ k then decide (num ≥ 10 ^ k.toNat * den) else decide (num * 10 ^ (-k).toNat ≥ den)

/-- The exponent `k` with `10 ^ k ≤ m * 2 ^ e < 10 ^ (k + 1)`, adjusted from the estimate `k`. -/
def decimalExponent (m : Nat) (e : Int) : (fuel : Nat) → (k : Int) → Int
  | 0, k => k
  | fuel + 1, k =>
    if !atLeastPowerOfTen m e k then decimalExponent m e fuel (k - 1)
    else if atLeastPowerOfTen m e (k + 1) then decimalExponent m e fuel (k + 1)
    else k

/--
`m * 2 ^ e`, `c * 10 ^ q`, and the half gaps above and below `m * 2 ^ e` in `spec`, all times
`2 ^ t * 10 ^ s`, where `t` and `s` are chosen so that every one of them is a natural number.
Below a power of two, the gap to the next smaller float is half as wide.
-/
def scaledAround (spec : Format) (m : Nat) (e : Int) (c : Nat) (q : Int) :
    Nat × Nat × Nat × Nat :=
  let t : Nat := (2 - e).toNat
  let s : Nat := (-q).toNat
  let e2 : Nat := (e + t).toNat
  let halfAbove := 2 ^ (e2 - 1) * 10 ^ s
  let halfBelow :=
    if m = 2 ^ spec.mantissaBitsWithoutImplicit ∧ e > spec.minExponent then 2 ^ (e2 - 2) * 10 ^ s
    else halfAbove
  (m * 2 ^ e2 * 10 ^ s, c * 10 ^ (q + s).toNat * 2 ^ t, halfAbove, halfBelow)

/--
Whether `c * 10 ^ q` reads back to the float `m * 2 ^ e` in `spec`.  Ties read back to the float
with the even mantissa, so the boundaries count when `m` is even.
-/
def readsBack (spec : Format) (m : Nat) (e : Int) (c : Nat) (q : Int) : Bool :=
  let (value, candidate, halfAbove, halfBelow) := scaledAround spec m e c q
  let inclusive := m % 2 = 0
  if value ≤ candidate then
    if inclusive then decide (candidate - value ≤ halfAbove)
    else decide (candidate - value < halfAbove)
  else
    if inclusive then decide (value - candidate ≤ halfBelow)
    else decide (value - candidate < halfBelow)

/--
The shortest digits `c` and exponent `q` such that `c * 10 ^ q` reads back to `m * 2 ^ e`, trying
`p` significant digits upwards.  With `p` digits the candidates are the multiples of `10 ^ q` just
below and just above `m * 2 ^ e`.
-/
def shortestDecimalAux (spec : Format) (m : Nat) (e k : Int) :
    (fuel : Nat) → (p : Nat) → Nat × Int
  | 0, _ => (scaleFloor m e (16 - k), k - 16)
  | fuel + 1, p =>
    let q := k - (p - 1 : Nat)
    let below := scaleFloor m e (-q)
    match readsBack spec m e below q, readsBack spec m e (below + 1) q with
    | false, false => shortestDecimalAux spec m e k fuel (p + 1)
    | true, false => (below, q)
    | false, true => (below + 1, q)
    | true, true =>
      -- the nearer of the two: compare `m * 2 ^ e` with the midpoint `(below + 1/2) * 10 ^ q`
      let (value, mid, _, _) := scaledAround spec m e (2 * below + 1) q
      if 2 * value < mid then (below, q)
      else if 2 * value > mid then (below + 1, q)
      else if below % 2 = 0 then (below, q) else (below + 1, q)

/-- The shortest digits and exponent for the positive float `m * 2 ^ e` in `spec`. -/
def shortestDecimal (spec : Format) (m : Nat) (e : Int) : Nat × Int :=
  let k := decimalExponent m e 8 ((Nat.log2 m + e) * 30103 / 100000)
  shortestDecimalAux spec m e k (spec.mantissaBits + 2) 1

/-- The decimal digits of `n`, most significant first, prepended to `acc`. -/
def decimalDigits : (fuel n : Nat) → (acc : List Char) → List Char
  | 0, _, acc => acc
  | fuel + 1, n, acc =>
    let acc := Char.ofNat ('0'.toNat + n % 10) :: acc
    if n < 10 then acc else decimalDigits fuel (n / 10) acc

/-- Appends the characters `cs` to `s`. -/
def pushAll (s : String) : List Char → String
  | [] => s
  | c :: cs => pushAll (s.push c) cs

/-- Appends `n` copies of `c` to `s`. -/
def pushZeros (s : String) : Nat → String
  | 0 => s
  | n + 1 => pushZeros (s.push '0') n

/--
Lays out the digits `c` (without trailing zeros) times `10 ^ q` as Python's `repr` does:
positional notation when the decimal point falls within the digits or up to four places before or
sixteen after them, scientific notation otherwise, and always a `.` or an `e`.
-/
def layoutDecimal (s : String) (c : Nat) (q : Int) : String :=
  let ds := decimalDigits (Nat.log2 c + 2) c []
  let n := ds.length
  -- the value is `0.<ds> * 10 ^ point`
  let point : Int := n + q
  if point ≤ -4 ∨ point > 16 then
    let s := pushAll s (ds.take 1)
    let s := if n > 1 then pushAll (s.push '.') (ds.drop 1) else s
    let exp := point - 1
    let s := (s.push 'e').push (if exp < 0 then '-' else '+')
    let s := if exp.natAbs < 10 then s.push '0' else s
    pushAll s (decimalDigits (Nat.log2 exp.natAbs + 2) exp.natAbs [])
  else if point ≤ 0 then
    pushAll (pushZeros ((s.push '0').push '.') (-point).toNat) ds
  else if n ≤ point.toNat then
    pushAll (pushZeros (pushAll s ds) (point.toNat - n)) ['.', '0']
  else
    pushAll (pushAll s (ds.take point.toNat) |>.push '.') (ds.drop point.toNat)

/-- Removes trailing zeros from `c * 10 ^ q`. -/
def stripTrailingZeros : (fuel c : Nat) → (q : Int) → Nat × Int
  | 0, c, q => (c, q)
  | fuel + 1, c, q =>
    if c % 10 = 0 ∧ c ≠ 0 then stripTrailingZeros fuel (c / 10) (q + 1) else (c, q)

/-- The logical model of `Float.toString` and `Float32.toString` for floats in `spec`. -/
def toDecimalString (spec : Format) : UnpackedFloat → String
  | .notANumber => "NaN"
  | .infinity .positive => "inf"
  | .infinity .negative => "-inf"
  | .zero .positive => "0.0"
  | .zero .negative => "-0.0"
  | .finite sign m e _ =>
    let (c, q) := shortestDecimal spec m e
    let (c, q) := stripTrailingZeros (Nat.log2 c + 2) c q
    layoutDecimal (if sign = .negative then "-" else "") c q

/-- The shortest decimal that reads back to the same value, as `Float.toString` writes it. -/
def modelToString (a : Float.Model) : String :=
  toDecimalString .binary64 a.unpack

end FloatRoundtrip
