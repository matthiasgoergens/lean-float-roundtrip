import FloatRoundtrip.Round

/-!
# Reading a decimal back

`UnpackedFloat.ofScientific spec c q` rounds `c * 10 ^ q` to `spec`.  This file shows that it gives
the canonical float `m * 2 ^ e` whenever `c * 10 ^ q` is near it: on the `mul` path for `q ≥ 0`,
on the `div` path for `q < 0`, and never in the two early exits for huge exponents.
-/

open Float.Model Float.Model.UnpackedFloat

namespace FloatRoundtrip

theorem describes_exact (M : ℕ) : Describes (.ofMantissaAndAccuracy M .exact) M := by
  simp [Describes, ExtendedMantissa.ofMantissaAndAccuracy]

/-- An inexact accuracy `o` describes `q + f` for a fraction `0 < f < 1` on the side `o` of `1/2`. -/
theorem describes_inexact (q : ℕ) {f : ℚ} (h0 : 0 < f) (h1 : f < 1) :
    Describes (.ofMantissaAndAccuracy q (.inexact (compare f (1 / 2)))) (q + f) := by
  rcases lt_trichotomy f (1 / 2) with h | h | h
  · rw [compare_lt_iff_lt.2 h]
    simp only [Describes, ExtendedMantissa.ofMantissaAndAccuracy, Bool.false_eq_true, false_iff,
      true_iff, not_le, ne_eq]
    refine ⟨by linarith, by linarith, by linarith, fun e => by linarith, fun e => by linarith⟩
  · rw [compare_eq_iff_eq.2 h]
    simp only [Describes, ExtendedMantissa.ofMantissaAndAccuracy, Bool.false_eq_true, false_iff,
      true_iff, ne_eq, not_and_or, not_not]
    refine ⟨by linarith, by linarith, by linarith, Or.inr (by linarith)⟩
  · rw [compare_gt_iff_gt.2 h]
    simp only [Describes, ExtendedMantissa.ofMantissaAndAccuracy, true_iff, ne_eq]
    refine ⟨by linarith, by linarith, by linarith, fun e => by linarith, fun e => by linarith⟩

/-- `divCore`'s quotient, with the accuracy of its remainder, describes the exact quotient. -/
theorem describes_div (N D : ℕ) (hD : 0 < D) :
    Describes (.ofMantissaAndAccuracy (N / D) (accuracyOfFraction (N % D) D)) ((N : ℚ) / D) := by
  have hDQ : (0 : ℚ) < D := by exact_mod_cast hD
  have hN : (N : ℚ) / D = (N / D : ℕ) + ((N % D : ℕ) : ℚ) / D := by
    rw [div_eq_iff hDQ.ne', add_mul, div_mul_cancel₀ _ hDQ.ne']
    exact_mod_cast (Nat.div_add_mod' N D).symm
  have hltQ : ((N % D : ℕ) : ℚ) < D := by exact_mod_cast Nat.mod_lt _ hD
  rw [hN]
  simp only [accuracyOfFraction]
  split_ifs with hr0
  · simpa [hr0] using describes_exact (N / D)
  · have hpos : (0 : ℚ) < ((N % D : ℕ) : ℚ) / D := by
      have : (0 : ℚ) < ((N % D : ℕ) : ℚ) := by exact_mod_cast Nat.pos_of_ne_zero hr0
      positivity
    have hcmp : compare (2 * (N % D)) D = compare (((N % D : ℕ) : ℚ) / D) (1 / 2) := by
      have hiff : ((N % D : ℕ) : ℚ) / D < 1 / 2 ↔ 2 * (N % D) < D := by
        rw [div_lt_iff₀ hDQ]; constructor <;> intro h
        · exact_mod_cast (by linarith : (2 * (N % D : ℕ) : ℚ) < D)
        · have : (2 * (N % D : ℕ) : ℚ) < D := by exact_mod_cast h
          linarith
      rcases lt_trichotomy (2 * (N % D)) D with h | h | h
      · rw [compare_lt_iff_lt.2 h, compare_lt_iff_lt.2 (hiff.2 h)]
      · rw [compare_eq_iff_eq.2 h, compare_eq_iff_eq.2]
        rw [div_eq_iff hDQ.ne']
        have : (2 * (N % D : ℕ) : ℚ) = D := by exact_mod_cast h
        linarith
      · rw [compare_gt_iff_gt.2 h, compare_gt_iff_gt.2]
        rw [lt_div_iff₀ hDQ]
        have : (D : ℚ) < 2 * (N % D : ℕ) := by exact_mod_cast h
        linarith
    rw [hcmp]
    exact describes_inexact _ hpos ((div_lt_one hDQ).2 hltQ)

/-- `div` of two positive finite floats, with `divCore`'s `let`s spelled out. -/
theorem div_finite_eq (spec : Format) (m₁ : ℕ) (e₁ : ℤ) (m₂ : ℕ) (e₂ : ℤ) (h₁ : 0 < m₁)
    (h₂ : 0 < m₂) :
    div spec (.finite .positive m₁ e₁ h₁) (.finite .positive m₂ e₂ h₂) =
      let T := min (e₁ - e₂) (spec.targetExponent (totalExponent m₁ e₁ - totalExponent m₂ e₂))
      let N := m₁ <<< (e₁ - e₂ - T).toNat
      roundWithAccuracy spec .positive (N / m₂) T (accuracyOfFraction (N % m₂) m₂) := rfl

theorem mul_finite_eq (spec : Format) (m₁ : ℕ) (e₁ : ℤ) (m₂ : ℕ) (e₂ : ℤ) (h₁ : 0 < m₁)
    (h₂ : 0 < m₂) :
    mul spec (.finite .positive m₁ e₁ h₁) (.finite .positive m₂ e₂ h₂) =
      roundWithAccuracy spec .positive (m₁ * m₂) (e₁ + e₂) .exact := rfl

theorem Canonical.lt_two_pow {spec : Format} {m : ℕ} {e : ℤ} (hc : Canonical spec m e) :
    m < 2 ^ spec.mantissaBits := by
  obtain ⟨hm, he⟩ := hc
  simp only [Format.targetExponent, totalExponent] at he
  have : m.log2 + 1 ≤ spec.mantissaBits := by omega
  calc m < 2 ^ (m.log2 + 1) := Nat.lt_log2_self
    _ ≤ 2 ^ spec.mantissaBits := Nat.pow_le_pow_right (by norm_num) this

theorem Canonical.minExponent_le {spec : Format} {m : ℕ} {e : ℤ} (hc : Canonical spec m e) :
    spec.minExponent ≤ e := by
  have := hc.2; simp only [Format.targetExponent] at this; omega

theorem two_zpow_le_ten_zpow {n : ℤ} (hn : 0 ≤ n) : (2 : ℚ) ^ n ≤ 10 ^ n := by
  lift n to ℕ using hn
  simp only [zpow_natCast]; gcongr; norm_num

theorem ten_zpow_le_two_zpow {n : ℤ} (hn : n ≤ 0) : (10 : ℚ) ^ n ≤ 2 ^ n := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = -k := ⟨n.natAbs, by omega⟩
  simp only [zpow_neg, zpow_natCast]
  gcongr; norm_num

/--
`ofScientific` reads `c * 10 ^ q` back as the canonical float `m * 2 ^ e` when the decimal is
near it.  The two conditions on `spec` hold for `binary32` and `binary64`; the bound on `e` holds
for every finite float that `unpack` produces.
-/
theorem ofScientific_of_near {spec : Format} {c : ℕ} (hc0 : 0 < c) {q : ℤ} {m : ℕ} {e : ℤ}
    (hcan : Canonical spec m e) (hmax : e + spec.mantissaBits ≤ 2 ^ spec.exponentBits)
    (hspec : spec.mantissaBits ≤ 2 ^ (spec.exponentBits - 1))
    (hn : Near spec m e (c * 10 ^ q)) :
    UnpackedFloat.ofScientific spec c q = .finite .positive m e hcan.1 := by
  have hm := hcan.1
  have hmlt := hcan.lt_two_pow
  have hmin := hcan.minExponent_le
  obtain ⟨hy₁, hy₂⟩ := near_bounds hn
  have h2e : (0 : ℚ) < 2 ^ e := zpow_pos two_pos e
  have hcQ : (1 : ℚ) ≤ c := by exact_mod_cast hc0
  set r : ℚ := c * 10 ^ q with hr
  have hr' : r = r / 2 ^ e * 2 ^ e := by field_simp
  have heb : (2 : ℤ) ^ spec.exponentBits = 2 * 2 ^ (spec.exponentBits - 1) := by
    rw [← pow_succ']; congr 1; have := spec.he; omega
  have hspec' : (spec.mantissaBits : ℤ) ≤ 2 ^ (spec.exponentBits - 1) := by exact_mod_cast hspec
  unfold UnpackedFloat.ofScientific
  rw [dif_neg (by omega)]
  split_ifs with h₁ h₂ h₃
  · -- `q` so large that `c * 10 ^ q` is beyond every finite float
    exfalso
    have hmlt' : (m : ℚ) + 1 / 2 < 2 ^ (spec.mantissaBits : ℤ) := by
      rw [zpow_natCast]; have : (m : ℚ) + 1 ≤ 2 ^ spec.mantissaBits := by exact_mod_cast hmlt
      linarith
    have : r < r := by
      calc r = r / 2 ^ e * 2 ^ e := hr'
        _ ≤ (m + 1 / 2) * 2 ^ e := by gcongr
        _ < 2 ^ (spec.mantissaBits : ℤ) * 2 ^ e := by gcongr
        _ = 2 ^ ((spec.mantissaBits : ℤ) + e) := (zpow_add₀ two_ne_zero _ _).symm
        _ ≤ 2 ^ ((2 : ℤ) ^ spec.exponentBits) := by
            apply zpow_le_zpow_right₀ one_le_two; omega
        _ ≤ 10 ^ ((2 : ℤ) ^ spec.exponentBits) := two_zpow_le_ten_zpow (by positivity)
        _ ≤ 10 ^ q := by apply zpow_le_zpow_right₀ (by norm_num); omega
        _ = 1 * 10 ^ q := (one_mul _).symm
        _ ≤ c * 10 ^ q := by gcongr
    exact lt_irrefl _ this
  · -- `q` so small that `c * 10 ^ q` is below half the smallest subnormal
    exfalso
    have hlogc := succ_le_two_zpow_log2 c
    have hlow : (2 : ℚ) ^ (e - 1) ≤ r := by
      rw [zpow_sub₀ two_ne_zero, zpow_one]
      calc (2 : ℚ) ^ e / 2 = (1 - 1 / 2) * 2 ^ e := by ring
        _ ≤ (m - 1 / 2) * 2 ^ e := by
            gcongr; exact_mod_cast hm
        _ ≤ r / 2 ^ e * 2 ^ e := by gcongr
        _ = r := hr'.symm
    have hhigh : r < 2 ^ ((c.log2 : ℤ) + 1 + q) := by
      rw [zpow_add₀ two_ne_zero]
      calc r = c * 10 ^ q := rfl
        _ < (c + 1) * 10 ^ q := by gcongr; linarith
        _ ≤ 2 ^ ((c.log2 : ℤ) + 1) * 10 ^ q := by gcongr
        _ ≤ 2 ^ ((c.log2 : ℤ) + 1) * 2 ^ q := by gcongr; exact ten_zpow_le_two_zpow (by omega)
    have := lt_of_zpow_le_lt hlow hhigh
    simp only [Format.minExponent] at hmin
    omega
  · -- the `mul` path: `c * 2 ^ mb * 10 ^ q` at exponent `-mb`, exactly
    have hq : 0 ≤ q := by omega
    rw [mul_finite_eq]
    apply roundWithAccuracy_of_near .positive (describes_exact _) ?_ hcan ?_
    · simp only [Format.targetExponent, totalExponent]
      have hpos : 0 < c <<< spec.mantissaBits * 10 ^ q.toNat := by
        rw [Nat.shiftLeft_eq]; positivity
      have : spec.mantissaBits ≤ (c <<< spec.mantissaBits * 10 ^ q.toNat).log2 := by
        rw [Nat.le_log2 hpos.ne', Nat.shiftLeft_eq]
        calc 2 ^ spec.mantissaBits = 1 * 2 ^ spec.mantissaBits * 1 := by ring
          _ ≤ c * 2 ^ spec.mantissaBits * 10 ^ q.toNat := by
              gcongr
              · exact hc0
              · exact Nat.one_le_pow _ _ (by norm_num)
      omega
    · convert hn using 1
      rw [hr, Nat.shiftLeft_eq]; push_cast
      rw [zpow_add₀ two_ne_zero, zpow_neg, zpow_natCast, zpow_zero,
        ← zpow_natCast (10 : ℚ) q.toNat, Int.toNat_of_nonneg hq]
      field_simp
  · -- the `div` path: `c * 2 ^ sh / 10 ^ k` at exponent `-sh`
    have hq : q < 0 := by omega
    have hD : 0 < 10 ^ (-q).toNat := by positivity
    rw [div_finite_eq]
    simp only
    set T := min ((0 : ℤ) - 0)
      (spec.targetExponent (totalExponent c 0 - totalExponent (10 ^ (-q).toNat) 0)) with hT
    have hT0 : T ≤ 0 := by rw [hT]; exact min_le_left _ _
    have hsh : (((0 : ℤ) - 0 - T).toNat : ℤ) = -T := by rw [Int.toNat_of_nonneg (by omega)]; ring
    apply roundWithAccuracy_of_near .positive (describes_div _ _ hD) ?_ hcan ?_
    · by_cases hTm : T ≤ spec.minExponent
      · simp only [Format.targetExponent]; exact le_trans hTm (le_max_right _ _)
      · set D := 10 ^ (-q).toNat
        set N := c <<< ((0 : ℤ) - 0 - T).toNat
        have hTle : T ≤ (c.log2 : ℤ) - D.log2 - spec.mantissaBits := by
          simp only [Format.targetExponent, totalExponent] at hT; omega
        have hmb : 1 ≤ spec.mantissaBits := by
          have : spec.mantissaBits = 1 + spec.mantissaBitsWithoutImplicit := rfl; omega
        have hN : 2 ^ (spec.mantissaBits - 1) * D ≤ N := by
          have hDlt : D < 2 ^ (D.log2 + 1) := Nat.lt_log2_self
          have hc2 : 2 ^ c.log2 ≤ c := Nat.log2_self_le hc0.ne'
          have hexp : spec.mantissaBits + D.log2 ≤ c.log2 + ((0 : ℤ) - 0 - T).toNat := by omega
          calc 2 ^ (spec.mantissaBits - 1) * D
              ≤ 2 ^ (spec.mantissaBits - 1) * 2 ^ (D.log2 + 1) := by gcongr
            _ = 2 ^ (spec.mantissaBits + D.log2) := by
                rw [← pow_add]; congr 1; omega
            _ ≤ 2 ^ (c.log2 + ((0 : ℤ) - 0 - T).toNat) :=
                Nat.pow_le_pow_right (by norm_num) hexp
            _ = 2 ^ c.log2 * 2 ^ ((0 : ℤ) - 0 - T).toNat := pow_add _ _ _
            _ ≤ c * 2 ^ ((0 : ℤ) - 0 - T).toNat := by gcongr
            _ = N := (Nat.shiftLeft_eq _ _).symm
        have hQ : 2 ^ (spec.mantissaBits - 1) ≤ N / D := (Nat.le_div_iff_mul_le hD).2 hN
        have hlog : spec.mantissaBits - 1 ≤ (N / D).log2 :=
          (Nat.le_log2 (by have := Nat.one_le_two_pow (n := spec.mantissaBits - 1); omega)).2 hQ
        simp only [Format.targetExponent, totalExponent]
        omega
    · convert hn using 1
      rw [hr, Nat.shiftLeft_eq]
      have h2 : ((2 ^ ((0 : ℤ) - 0 - T).toNat : ℕ) : ℚ) = (2 : ℚ) ^ (-T) := by
        rw [Nat.cast_pow, Nat.cast_ofNat, ← zpow_natCast, hsh]
      have h10 : ((10 ^ (-q).toNat : ℕ) : ℚ) = (10 : ℚ) ^ (-q) := by
        rw [Nat.cast_pow, Nat.cast_ofNat, ← zpow_natCast, Int.toNat_of_nonneg (by omega)]
      rw [Nat.cast_mul, h2, h10, zpow_neg, zpow_neg]
      field_simp

end FloatRoundtrip
