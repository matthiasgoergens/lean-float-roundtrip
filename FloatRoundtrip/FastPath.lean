import FloatRoundtrip.RoundTrip

/-!
# The fast path of `Float.ofScientific`

`Float.ofScientific c s k` does not always go through the model: when `c < 2 ^ 53` and `k ≤ 22`,
both `c` and `10 ^ k` are exact doubles, and it divides or multiplies them as floats.  This file
shows that the fast path reads a decimal near a float back as that float too, so that
`Float.ofScientific` agrees with the model's reading on every input near a float.
-/

open Float.Model Float.Model.UnpackedFloat

namespace FloatRoundtrip

/-- `div` of two positive finite floats lands on the canonical float near their quotient. -/
theorem div_of_near {spec : Format} {m₁ m₂ : ℕ} {e₁ e₂ : ℤ} (h₁ : 0 < m₁) (h₂ : 0 < m₂)
    {m : ℕ} {e : ℤ} (hcan : Canonical spec m e)
    (hn : Near spec m e (m₁ * 2 ^ e₁ / (m₂ * 2 ^ e₂))) :
    div spec (.finite .positive m₁ e₁ h₁) (.finite .positive m₂ e₂ h₂) =
      .finite .positive m e hcan.1 := by
  rw [div_finite_eq]
  simp only
  set T := min (e₁ - e₂)
    (spec.targetExponent (totalExponent m₁ e₁ - totalExponent m₂ e₂)) with hT
  have hT0 : T ≤ e₁ - e₂ := by rw [hT]; exact min_le_left _ _
  have hsh : ((e₁ - e₂ - T).toNat : ℤ) = e₁ - e₂ - T := Int.toNat_of_nonneg (by omega)
  apply roundWithAccuracy_of_near .positive (describes_div _ _ h₂) ?_ hcan ?_
  · by_cases hTm : T ≤ spec.minExponent
    · simp only [Format.targetExponent]; exact le_trans hTm (le_max_right _ _)
    · set N := m₁ <<< (e₁ - e₂ - T).toNat
      have hTle : T ≤ (m₁.log2 : ℤ) + 1 + e₁ - ((m₂.log2 : ℤ) + 1 + e₂) - spec.mantissaBits := by
        simp only [Format.targetExponent, totalExponent] at hT; omega
      have hmb : 1 ≤ spec.mantissaBits := by
        have : spec.mantissaBits = 1 + spec.mantissaBitsWithoutImplicit := rfl; omega
      have hN : 2 ^ (spec.mantissaBits - 1) * m₂ ≤ N := by
        have hDlt : m₂ < 2 ^ (m₂.log2 + 1) := Nat.lt_log2_self
        have hc2 : 2 ^ m₁.log2 ≤ m₁ := Nat.log2_self_le h₁.ne'
        have hexp : spec.mantissaBits + m₂.log2 ≤ m₁.log2 + (e₁ - e₂ - T).toNat := by omega
        calc 2 ^ (spec.mantissaBits - 1) * m₂
            ≤ 2 ^ (spec.mantissaBits - 1) * 2 ^ (m₂.log2 + 1) := by gcongr
          _ = 2 ^ (spec.mantissaBits + m₂.log2) := by rw [← pow_add]; congr 1; omega
          _ ≤ 2 ^ (m₁.log2 + (e₁ - e₂ - T).toNat) := Nat.pow_le_pow_right (by norm_num) hexp
          _ = 2 ^ m₁.log2 * 2 ^ (e₁ - e₂ - T).toNat := pow_add _ _ _
          _ ≤ m₁ * 2 ^ (e₁ - e₂ - T).toNat := by gcongr
          _ = N := (Nat.shiftLeft_eq _ _).symm
      have hQ : 2 ^ (spec.mantissaBits - 1) ≤ N / m₂ := (Nat.le_div_iff_mul_le h₂).2 hN
      have hlog : spec.mantissaBits - 1 ≤ (N / m₂).log2 :=
        (Nat.le_log2 (by have := Nat.one_le_two_pow (n := spec.mantissaBits - 1); omega)).2 hQ
      simp only [Format.targetExponent, totalExponent]
      omega
  · convert hn using 1
    rw [Nat.shiftLeft_eq]
    have h2 : ((2 ^ (e₁ - e₂ - T).toNat : ℕ) : ℚ) = (2 : ℚ) ^ (e₁ - e₂ - T) := by
      rw [Nat.cast_pow, Nat.cast_ofNat, ← zpow_natCast, hsh]
    rw [Nat.cast_mul, h2, zpow_sub₀ two_ne_zero, zpow_sub₀ two_ne_zero]
    field_simp

/-- `mul` of two positive finite floats lands on the canonical float near their product. -/
theorem mul_of_near {spec : Format} {m₁ m₂ : ℕ} {e₁ e₂ : ℤ} (h₁ : 0 < m₁) (h₂ : 0 < m₂)
    (hbig : 2 ^ (spec.mantissaBits - 1) ≤ m₁ * m₂) {m : ℕ} {e : ℤ} (hcan : Canonical spec m e)
    (hn : Near spec m e (m₁ * 2 ^ e₁ * (m₂ * 2 ^ e₂))) :
    mul spec (.finite .positive m₁ e₁ h₁) (.finite .positive m₂ e₂ h₂) =
      .finite .positive m e hcan.1 := by
  rw [mul_finite_eq]
  apply roundWithAccuracy_of_near .positive (describes_exact _) ?_ hcan ?_
  · have hlog : spec.mantissaBits - 1 ≤ (m₁ * m₂).log2 :=
      (Nat.le_log2 (by positivity)).2 hbig
    have hmb : 1 ≤ spec.mantissaBits := by
      have : spec.mantissaBits = 1 + spec.mantissaBitsWithoutImplicit := rfl; omega
    simp only [Format.targetExponent, totalExponent]
    omega
  · convert hn using 1
    push_cast; rw [zpow_add₀ two_ne_zero]; ring

/-- The canonical form of a positive integer below `2 ^ 53`: its mantissa shifted to 53 bits. -/
theorem canonical_of_nat {c : ℕ} (hc0 : 0 < c) (hc : c < 2 ^ 53) :
    Canonical .binary64 (c <<< (52 - c.log2)) ((c.log2 : ℤ) - 52) ∧
      (c <<< (52 - c.log2)).log2 = 52 := by
  have hlog : c.log2 < 53 := (Nat.log2_lt hc0.ne').2 hc
  have hlo : 2 ^ c.log2 ≤ c := Nat.log2_self_le hc0.ne'
  have hhi : c < 2 ^ (c.log2 + 1) := Nat.lt_log2_self
  have hM : (c <<< (52 - c.log2)).log2 = 52 := by
    rw [Nat.shiftLeft_eq]
    apply log2_eq_of_bounds
    · calc 2 ^ 52 = 2 ^ c.log2 * 2 ^ (52 - c.log2) := by rw [← pow_add]; congr 1; omega
        _ ≤ c * 2 ^ (52 - c.log2) := by gcongr
    · calc c * 2 ^ (52 - c.log2) < 2 ^ (c.log2 + 1) * 2 ^ (52 - c.log2) := by gcongr
        _ = 2 ^ (52 + 1) := by rw [← pow_add]; congr 1; omega
  refine ⟨⟨by rw [Nat.shiftLeft_eq]; positivity, ?_⟩, hM⟩
  simp only [Format.targetExponent, totalExponent, hM, binary64_minExponent, binary64_mantissaBits]
  omega

/-- A positive integer below `2 ^ 53` converts exactly. -/
theorem toFloat_unpack {c : ℕ} (hc0 : 0 < c) (hc : c < 2 ^ 53) :
    (c.toUInt64.toFloat).toModel.unpack =
      .finite .positive (c <<< (52 - c.log2)) ((c.log2 : ℤ) - 52)
        (canonical_of_nat hc0 hc).1.1 := by
  obtain ⟨hcan, hM⟩ := canonical_of_nat hc0 hc
  have hlog : c.log2 < 53 := (Nat.log2_lt hc0.ne').2 hc
  have hround : UnpackedFloat.ofUInt64 .binary64 c.toUInt64 =
      .finite .positive (c <<< (52 - c.log2)) ((c.log2 : ℤ) - 52) hcan.1 := by
    have htoNat : c.toUInt64.toNat = c := by
      have : c < 18446744073709551616 := by omega
      simpa using this
    simp only [UnpackedFloat.ofUInt64, UnpackedFloat.ofNat, UnpackedFloat.ofInt,
      UnpackedFloat.normalize, htoNat]
    have hcmp : compare (c : ℤ) 0 = .gt := compare_gt_iff_gt.2 (by exact_mod_cast hc0)
    rw [hcmp]
    simp only [UnpackedFloat.round, decreaseExponent, Int.toNat_natCast]
    have ht : Format.binary64.targetExponent (totalExponent c 0) = (c.log2 : ℤ) - 52 := by
      simp only [Format.targetExponent, totalExponent, binary64_minExponent, binary64_mantissaBits]
      omega
    have hsh : (0 - Format.binary64.targetExponent (totalExponent c 0)).toNat = 52 - c.log2 := by
      rw [ht]; omega
    have hE : (0 : ℤ) - ((52 - c.log2 : ℕ) : ℤ) = (c.log2 : ℤ) - 52 := by omega
    simp only [hsh, hE]
    apply roundWithAccuracy_of_near .positive (describes_exact _) ?_ hcan ?_
    · simp only [Format.targetExponent, totalExponent, hM, binary64_minExponent,
        binary64_mantissaBits]
      omega
    · left
      rw [mul_div_assoc, div_self (zpow_pos (two_pos : (0 : ℚ) < 2) _).ne', mul_one]
      exact ⟨le_rfl, Or.inl (by norm_num)⟩
  show Float.Model.unpack (Float.Model.pack _) = _
  rw [hround]
  exact model_unpack_pack hcan (by omega)

/-- The bit patterns of `Float.exactlyRepresentablePowersOfTen`, as in its definition. -/
def tableBits : List UInt64 :=
  [0x3FF0000000000000, 0x4024000000000000, 0x4059000000000000, 0x408F400000000000,
   0x40C3880000000000, 0x40F86A0000000000, 0x412E848000000000, 0x416312D000000000,
   0x4197D78400000000, 0x41CDCD6500000000, 0x4202A05F20000000, 0x42374876E8000000,
   0x426D1A94A2000000, 0x42A2309CE5400000, 0x42D6BCC41E900000, 0x430C6BF526340000,
   0x4341C37937E08000, 0x4376345785D8A000, 0x43ABC16D674EC800, 0x43E158E460913D00,
   0x4415AF1D78B58C40, 0x444B1AE4D6E2EF50, 0x4480F0CF064DD592]

theorem table_eq : Float.exactlyRepresentablePowersOfTen = (tableBits.map Float.ofBits).toArray :=
  rfl

/-- Whether the bit pattern `b` unpacks to the positive finite float `10 ^ i`. -/
def powCheck (b : UInt64) (i : ℕ) : Bool :=
  match UnpackedFloat.unpack .binary64 b.toBitVec with
  | .finite .positive P F _ =>
    if 0 ≤ F then P * 2 ^ F.toNat == 10 ^ i else P == 10 ^ i * 2 ^ (-F).toNat
  | _ => false

theorem table_check : ∀ i : Fin 23, powCheck (tableBits[i.1]'(by simp [tableBits])) i = true := by
  decide +kernel

theorem powCheck_spec {b : UInt64} {i : ℕ} (h : powCheck b i = true) :
    ∃ P F hP, UnpackedFloat.unpack .binary64 b.toBitVec = .finite .positive P F hP ∧
      (P : ℚ) * 2 ^ F = 10 ^ i := by
  unfold powCheck at h
  generalize hu : UnpackedFloat.unpack .binary64 b.toBitVec = u at h
  rcases u with _ | _ | _ | ⟨_ | _, P, F, hP⟩ <;> simp only [Bool.false_eq_true] at h
  refine ⟨P, F, hP, rfl, ?_⟩
  split_ifs at h with hF
  · have h' : P * 2 ^ F.toNat = 10 ^ i := by simpa using h
    rw [two_zpow_of_nonneg hF]; exact_mod_cast h'
  · have h' : P = 10 ^ i * 2 ^ (-F).toNat := by simpa using h
    rw [two_zpow_of_neg hF, h']; push_cast; field_simp

/-- The table entries are the exact powers of ten. -/
theorem table_unpack (i : ℕ) (hi : i ≤ 22) :
    ∃ P F hP, (Float.exactlyRepresentablePowersOfTen[i]'(by simp [table_eq, tableBits]; omega)).toModel.unpack =
      .finite .positive P F hP ∧ (P : ℚ) * 2 ^ F = 10 ^ i := by
  obtain ⟨P, F, hP, hu, hv⟩ := powCheck_spec (table_check ⟨i, by omega⟩)
  refine ⟨P, F, hP, ?_, hv⟩
  obtain ⟨hcan, he⟩ := unpack_finite hu
  have hentry : (Float.exactlyRepresentablePowersOfTen[i]'(by simp [table_eq, tableBits]; omega)) =
      Float.ofBits (tableBits[i]'(by simp [tableBits]; omega)) := by
    simp only [table_eq, List.getElem_toArray, List.getElem_map]
  rw [hentry]
  show Float.Model.unpack (Float.Model.pack (UnpackedFloat.unpack .binary64 _)) = _
  rw [hu]
  exact model_unpack_pack hcan he

theorem float_ext {a b : Float} (h : a.toModel = b.toModel) : a = b := by
  cases a; cases b; cases h; rfl

theorem shifted_value {c : ℕ} (hc0 : 0 < c) (hc : c < 2 ^ 53) :
    ((c <<< (52 - c.log2) : ℕ) : ℚ) * 2 ^ ((c.log2 : ℤ) - 52) = c := by
  have hlog : c.log2 < 53 := (Nat.log2_lt hc0.ne').2 hc
  rw [Nat.shiftLeft_eq]; push_cast
  rw [← zpow_natCast, mul_assoc, ← zpow_add₀ two_ne_zero,
    show (((52 - c.log2 : ℕ)) : ℤ) + ((c.log2 : ℤ) - 52) = 0 by omega, zpow_zero, mul_one]

/--
`Float.ofScientific`, fast path included, reads a decimal near the canonical float `m * 2 ^ e`
back as that float.
-/
theorem floatOfScientific_of_near {c : ℕ} {q : ℤ} {m : ℕ} {e : ℤ} (hcan : Canonical .binary64 m e)
    (he : e ≤ 971) (hn : Near .binary64 m e (c * 10 ^ q)) :
    (Float.ofScientific c (decide (q < 0)) q.natAbs).toModel =
      Float.Model.pack (.finite .positive m e hcan.1) := by
  have hc0 := hn.digits_pos hcan.1
  unfold Float.ofScientific
  split_ifs with hfast hneg hneg
  · -- fast path, division by `10 ^ |q|`
    have hq : q < 0 := by simpa using hneg
    obtain ⟨P, F, hP, hu, hv⟩ := table_unpack q.natAbs hfast.2
    show Float.Model.pack (UnpackedFloat.div .binary64 (c.toUInt64.toFloat).toModel.unpack
      (Float.exactlyRepresentablePowersOfTen[q.natAbs]'_).toModel.unpack) = _
    rw [toFloat_unpack hc0 hfast.1, hu, div_of_near _ hP hcan]
    convert hn using 1
    rw [shifted_value hc0 hfast.1, hv, ← zpow_natCast, Int.natCast_natAbs, abs_of_neg hq,
      zpow_neg, div_eq_mul_inv, inv_inv]
  · -- fast path, multiplication by `10 ^ q`
    have hq : 0 ≤ q := by simpa using hneg
    obtain ⟨P, F, hP, hu, hv⟩ := table_unpack q.natAbs hfast.2
    show Float.Model.pack (UnpackedFloat.mul .binary64 (c.toUInt64.toFloat).toModel.unpack
      (Float.exactlyRepresentablePowersOfTen[q.natAbs]'_).toModel.unpack) = _
    obtain ⟨hcan₁, hM⟩ := canonical_of_nat hc0 hfast.1
    have hM52 : 2 ^ 52 ≤ c <<< (52 - c.log2) := by
      have := Nat.log2_self_le hcan₁.1.ne'; rwa [hM] at this
    rw [toFloat_unpack hc0 hfast.1, hu, mul_of_near _ hP (by
      simp only [binary64_mantissaBits]; calc 2 ^ (53 - 1) ≤ c <<< (52 - c.log2) := hM52
        _ ≤ (c <<< (52 - c.log2)) * P := Nat.le_mul_of_pos_right _ hP) hcan]
    convert hn using 1
    rw [shifted_value hc0 hfast.1, hv, ← zpow_natCast, Int.natCast_natAbs, abs_of_nonneg hq]
  · -- the model, for a negative exponent
    have hq : q < 0 := by simpa using hneg
    show Float.Model.ofScientific c (Int.negOfNat q.natAbs) = _
    rw [show Int.negOfNat q.natAbs = q by
      rw [Int.negOfNat_eq, Int.ofNat_eq_coe, Int.natCast_natAbs, abs_of_neg hq, neg_neg]]
    exact modelOfScientific_of_near hcan he hn
  · -- the model, for a nonnegative exponent
    have hq : 0 ≤ q := by simpa using hneg
    show Float.Model.ofScientific c (Int.ofNat q.natAbs) = _
    rw [show Int.ofNat q.natAbs = q by
      rw [Int.ofNat_eq_coe, Int.natCast_natAbs, abs_of_nonneg hq]]
    exact modelOfScientific_of_near hcan he hn

/--
**The round trip for `Float`.**  For every finite nonzero float `x`, reading back the digits and
exponent that the printer writes for it with `Float.ofScientific`, and negating if `x` is
negative, gives `x` again.
-/
theorem floatOfScientific_printedDigits (x : Float) {s : Sign} {m : ℕ} {e : ℤ} {h : 0 < m}
    (hx : x.toModel.unpack = .finite s m e h) :
    (if s = .negative then
      -Float.ofScientific (printedDigits m e).1 (decide ((printedDigits m e).2 < 0))
        (printedDigits m e).2.natAbs
    else Float.ofScientific (printedDigits m e).1 (decide ((printedDigits m e).2 < 0))
        (printedDigits m e).2.natAbs) = x := by
  obtain ⟨hc, he⟩ := unpack_finite hx
  have hfast := floatOfScientific_of_near hc he (printedDigits_near hc he)
  apply float_ext
  cases s with
  | positive =>
    simp only [reduceCtorEq, if_false]
    rw [hfast, ← pack_unpack x.toModel, hx]
  | negative =>
    simp only [if_true]
    show Float.Model.pack (Float.ofScientific _ _ _).toModel.unpack.neg = _
    rw [hfast, model_unpack_pack hc he, ← pack_unpack x.toModel, hx]
    rfl

end FloatRoundtrip
