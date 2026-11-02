import FloatRoundtrip.ReadsBack

/-!
# The printer always finds digits that read back

`shortestDecimal` estimates the decimal exponent `k` of `m * 2 ^ e`, corrects the estimate in at
most eight steps, and then tries one, two, three... significant digits until one of the two
candidates around `m * 2 ^ e` reads back.  This file shows that, for every canonical `binary64`
float, the correction succeeds within its fuel and seventeen digits always suffice, so the result
is always a pair that `readsBack` accepts.
-/

open Float.Model Float.Model.UnpackedFloat

namespace FloatRoundtrip

/-- Natural division is the floor of the rational quotient. -/
theorem floor_cast {a b : ℕ} (hb : 0 < b) {X : ℚ} (hX : (a : ℚ) / b = X) :
    ((a / b : ℕ) : ℚ) ≤ X ∧ X < (a / b : ℕ) + 1 := by
  have hbQ : (0 : ℚ) < b := by exact_mod_cast hb
  subst hX
  constructor
  · rw [le_div_iff₀ hbQ]; exact_mod_cast Nat.div_mul_le_self a b
  · rw [div_lt_iff₀ hbQ]
    have : (a : ℚ) < (a / b : ℕ) * b + b := by exact_mod_cast Nat.lt_div_mul_add hb
    linarith

theorem two_zpow_of_nonneg {e : ℤ} (he : 0 ≤ e) : (2 : ℚ) ^ e = ((2 ^ e.toNat : ℕ) : ℚ) := by
  rw [Nat.cast_pow, Nat.cast_ofNat, ← zpow_natCast, Int.toNat_of_nonneg he]

theorem two_zpow_of_neg {e : ℤ} (he : ¬0 ≤ e) : (2 : ℚ) ^ e = ((2 ^ (-e).toNat : ℕ) : ℚ)⁻¹ := by
  rw [Nat.cast_pow, Nat.cast_ofNat, ← zpow_natCast, Int.toNat_of_nonneg (by omega), zpow_neg,
    inv_inv]

theorem ten_zpow_of_nonneg {k : ℤ} (hk : 0 ≤ k) : (10 : ℚ) ^ k = ((10 ^ k.toNat : ℕ) : ℚ) := by
  rw [Nat.cast_pow, Nat.cast_ofNat, ← zpow_natCast, Int.toNat_of_nonneg hk]

theorem ten_zpow_of_neg {k : ℤ} (hk : ¬0 ≤ k) : (10 : ℚ) ^ k = ((10 ^ (-k).toNat : ℕ) : ℚ)⁻¹ := by
  rw [Nat.cast_pow, Nat.cast_ofNat, ← zpow_natCast, Int.toNat_of_nonneg (by omega), zpow_neg,
    inv_inv]

/-- `scaleFloor m e k` is `⌊m * 2 ^ e * 10 ^ k⌋`. -/
theorem scaleFloor_spec (m : ℕ) (e k : ℤ) :
    (scaleFloor m e k : ℚ) ≤ (m : ℚ) * 2 ^ e * 10 ^ k ∧
      (m : ℚ) * 2 ^ e * 10 ^ k < scaleFloor m e k + 1 := by
  by_cases he : 0 ≤ e <;> by_cases hk : 0 ≤ k <;>
    simp only [scaleFloor, he, hk, ite_true, ite_false]
  · refine floor_cast Nat.one_pos ?_
    rw [two_zpow_of_nonneg he, ten_zpow_of_nonneg hk]; push_cast; ring
  · refine floor_cast ?_ ?_
    · positivity
    · rw [two_zpow_of_nonneg he, ten_zpow_of_neg hk]; push_cast; field_simp
  · refine floor_cast ?_ ?_
    · positivity
    · rw [two_zpow_of_neg he, ten_zpow_of_nonneg hk]; push_cast; field_simp
  · refine floor_cast ?_ ?_
    · positivity
    · rw [two_zpow_of_neg he, ten_zpow_of_neg hk]; push_cast; field_simp

/-- `atLeastPowerOfTen m e k` decides `10 ^ k ≤ m * 2 ^ e`. -/
theorem atLeastPowerOfTen_iff (m : ℕ) (e k : ℤ) :
    atLeastPowerOfTen m e k = true ↔ (10 : ℚ) ^ k ≤ m * 2 ^ e := by
  by_cases he : 0 ≤ e <;> by_cases hk : 0 ≤ k <;>
    simp only [atLeastPowerOfTen, he, hk, ite_true, ite_false, decide_eq_true_eq, ge_iff_le]
  · rw [two_zpow_of_nonneg he, ten_zpow_of_nonneg hk, mul_one]; norm_cast
  · have hpos : (0 : ℚ) < ((10 ^ (-k).toNat : ℕ) : ℚ) := by positivity
    rw [two_zpow_of_nonneg he, ten_zpow_of_neg hk, inv_le_iff_one_le_mul₀ hpos]; norm_cast
  · have hpos : (0 : ℚ) < ((2 ^ (-e).toNat : ℕ) : ℚ) := by positivity
    rw [two_zpow_of_neg he, ten_zpow_of_nonneg hk, ← div_eq_mul_inv, le_div_iff₀ hpos]; norm_cast
  · have hpos₂ : (0 : ℚ) < ((2 ^ (-e).toNat : ℕ) : ℚ) := by positivity
    have hpos₁₀ : (0 : ℚ) < ((10 ^ (-k).toNat : ℕ) : ℚ) := by positivity
    rw [two_zpow_of_neg he, ten_zpow_of_neg hk, ← div_eq_mul_inv, inv_le_iff_one_le_mul₀ hpos₁₀,
      div_mul_eq_mul_div, le_div_iff₀ hpos₂, one_mul]; norm_cast

/--
For every binade `[2 ^ L, 2 ^ (L + 1))` of `binary64`, the printer's estimate `k₀` of the decimal
exponent is within seven of it: `10 ^ (k₀ - 7) ≤ 2 ^ L` and `2 ^ (L + 1) < 10 ^ (k₀ + 8)`.  Checked
by the kernel, one binade at a time.
-/
theorem estimate_check : ((List.range 2098).all fun i =>
    let L : ℤ := (i : ℤ) - 1074
    let k₀ := L * 30103 / 100000
    atLeastPowerOfTen 1 L (k₀ - 7) && !atLeastPowerOfTen 1 (L + 1) (k₀ + 8)) = true := by
  decide +kernel

theorem estimate_bounds {L : ℤ} (h₁ : -1074 ≤ L) (h₂ : L ≤ 1023) :
    (10 : ℚ) ^ (L * 30103 / 100000 - 7) ≤ 2 ^ L ∧
      (2 : ℚ) ^ (L + 1) < 10 ^ (L * 30103 / 100000 + 8) := by
  have h := List.all_eq_true.1 estimate_check (L + 1074).toNat (List.mem_range.2 (by omega))
  have hL : ((L + 1074).toNat : ℤ) - 1074 = L := by omega
  simp only [hL, Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨h1, h2⟩ := h
  rw [atLeastPowerOfTen_iff, Nat.cast_one, one_mul] at h1
  refine ⟨h1, ?_⟩
  by_contra hcon
  have : atLeastPowerOfTen 1 (L + 1) (L * 30103 / 100000 + 8) = true := by
    rw [atLeastPowerOfTen_iff, Nat.cast_one, one_mul]; exact not_lt.1 hcon
  rw [this] at h2; exact absurd h2 (by decide)

theorem lt_of_ten_zpow {a b : ℤ} {v : ℚ} (h₁ : (10 : ℚ) ^ a ≤ v) (h₂ : v < 10 ^ b) : a < b :=
  (zpow_lt_zpow_iff_right₀ (by norm_num : (1 : ℚ) < 10)).1 (lt_of_le_of_lt h₁ h₂)

/-- The correction loop reaches the decimal exponent `K` when it starts close enough to it. -/
theorem decimalExponent_eq {m : ℕ} {e K : ℤ} (hK₁ : (10 : ℚ) ^ K ≤ m * 2 ^ e)
    (hK₂ : (m : ℚ) * 2 ^ e < 10 ^ (K + 1)) :
    ∀ (fuel : ℕ) (k : ℤ), k - fuel < K → K < k + fuel → decimalExponent m e fuel k = K := by
  intro fuel
  induction fuel with
  | zero => intro k h₁ h₂; push_cast at h₁ h₂; omega
  | succ n ih =>
    intro k h₁ h₂
    push_cast at h₁ h₂
    cases ha : atLeastPowerOfTen m e k with
    | false =>
      have h3 : (m : ℚ) * 2 ^ e < 10 ^ k :=
        not_le.1 fun h => by rw [← atLeastPowerOfTen_iff, ha] at h; exact absurd h (by decide)
      have := lt_of_ten_zpow hK₁ h3
      simp only [decimalExponent, ha, Bool.not_false, ite_true]
      exact ih (k - 1) (by omega) (by omega)
    | true =>
      cases hb : atLeastPowerOfTen m e (k + 1) with
      | false =>
        have h3 : (m : ℚ) * 2 ^ e < 10 ^ (k + 1) :=
          not_le.1 fun h => by rw [← atLeastPowerOfTen_iff, hb] at h; exact absurd h (by decide)
        have := lt_of_ten_zpow ((atLeastPowerOfTen_iff _ _ _).1 ha) hK₂
        have := lt_of_ten_zpow hK₁ h3
        simp only [decimalExponent, ha, hb, Bool.not_true, Bool.false_eq_true, ite_false]
        omega
      | true =>
        have := lt_of_ten_zpow ((atLeastPowerOfTen_iff _ _ _).1 hb) hK₂
        simp only [decimalExponent, ha, hb, Bool.not_true, Bool.false_eq_true, ite_false, ite_true]
        exact ih (k + 1) (by omega) (by omega)

theorem binary64_minExponent : Format.binary64.minExponent = -1074 := by decide

/-- For a canonical `binary64` float, the printer's corrected exponent `k` has `10 ^ k ≤ m * 2 ^ e`. -/
theorem decimalExponent_binary64 {m : ℕ} {e : ℤ} (hc : Canonical .binary64 m e) (he : e ≤ 971) :
    (10 : ℚ) ^ (decimalExponent m e 8 ((Nat.log2 m + e) * 30103 / 100000)) ≤ m * 2 ^ e := by
  have hm := hc.1
  have hmlt : m < 2 ^ 53 := hc.lt_two_pow
  have hmin : -1074 ≤ e := binary64_minExponent ▸ hc.minExponent_le
  have hv : (0 : ℚ) < m * 2 ^ e := by
    have : (0 : ℚ) < m := by exact_mod_cast hm
    positivity
  have hK₁ : (10 : ℚ) ^ Int.log 10 ((m : ℚ) * 2 ^ e) ≤ m * 2 ^ e := by
    have := Int.zpow_log_le_self (b := 10) (by norm_num) hv; simpa using this
  have hK₂ : (m : ℚ) * 2 ^ e < 10 ^ (Int.log 10 ((m : ℚ) * 2 ^ e) + 1) := by
    have := Int.lt_zpow_succ_log_self (b := 10) (by norm_num) ((m : ℚ) * 2 ^ e); simpa using this
  have hlog : m.log2 < 53 := (Nat.log2_lt hm.ne').2 hmlt
  obtain ⟨hb₁, hb₂⟩ := estimate_bounds (L := (m.log2 : ℤ) + e) (by omega) (by omega)
  have hvL₁ : (2 : ℚ) ^ ((m.log2 : ℤ) + e) ≤ m * 2 ^ e := by
    rw [zpow_add₀ two_ne_zero]; gcongr; exact two_zpow_log2_le hm.ne'
  have hvL₂ : (m : ℚ) * 2 ^ e < 2 ^ ((m.log2 : ℤ) + e + 1) := by
    rw [show (m.log2 : ℤ) + e + 1 = ((m.log2 : ℤ) + 1) + e by ring, zpow_add₀ two_ne_zero]
    calc (m : ℚ) * 2 ^ e < (m + 1) * 2 ^ e := by gcongr; linarith
      _ ≤ 2 ^ ((m.log2 : ℤ) + 1) * 2 ^ e := by gcongr; exact succ_le_two_zpow_log2 m
  have h₁ := lt_of_ten_zpow (le_trans hb₁ hvL₁) hK₂
  have h₂ := lt_of_ten_zpow hK₁ (lt_trans hvL₂ hb₂)
  rw [decimalExponent_eq hK₁ hK₂ 8 _ (by push_cast; omega) (by push_cast; omega)]
  exact hK₁

/--
Seventeen significant digits always suffice: at `q = k - 16`, one of the two candidates around a
canonical `binary64` float `m * 2 ^ e ≥ 10 ^ k` reads back.  The spacing `10 ^ q` of the
candidates is below `2 ^ 53 / 10 ^ 16 < 1` unit of `2 ^ e`, and below a half at a power of two.
-/
theorem seventeen_digits {m : ℕ} {e k : ℤ} (hc : Canonical .binary64 m e)
    (hk : (10 : ℚ) ^ k ≤ m * 2 ^ e) :
    readsBack .binary64 m e (scaleFloor m e (-(k - 16))) (k - 16) = true ∨
      readsBack .binary64 m e (scaleFloor m e (-(k - 16)) + 1) (k - 16) = true := by
  rw [readsBack_iff_near, readsBack_iff_near]
  obtain ⟨hB₁, hB₂⟩ := scaleFloor_spec m e (-(k - 16))
  set B := scaleFloor m e (-(k - 16))
  have h2e : (0 : ℚ) < 2 ^ e := zpow_pos two_pos e
  have hu : (0 : ℚ) < 10 ^ (k - 16) := zpow_pos (by norm_num) _
  have hinv : (10 : ℚ) ^ (-(k - 16)) = (10 ^ (k - 16))⁻¹ := zpow_neg _ _
  rw [hinv, ← div_eq_mul_inv, le_div_iff₀ hu] at hB₁
  rw [hinv, ← div_eq_mul_inv, div_lt_iff₀ hu] at hB₂
  have hmlt : (m : ℚ) < 2 ^ 53 := by exact_mod_cast (hc.lt_two_pow : m < 2 ^ 53)
  have hspan : (10 : ℚ) ^ (k - 16) / 2 ^ e ≤ m / 10 ^ 16 := by
    rw [zpow_sub₀ (by norm_num), div_le_div_iff₀ h2e (by norm_num), zpow_ofNat]
    calc (10 : ℚ) ^ k / 10 ^ 16 * 10 ^ 16 = 10 ^ k := by field_simp
      _ ≤ m * 2 ^ e := hk
  set yB : ℚ := (B : ℚ) * 10 ^ (k - 16) / 2 ^ e with hyB
  set δ : ℚ := (10 : ℚ) ^ (k - 16) / 2 ^ e with hδ
  have hy₁ : yB ≤ m := by rw [hyB, div_le_iff₀ h2e]; exact hB₁
  have hy₂ : (m : ℚ) < yB + δ := by
    rw [hyB, hδ, ← add_div, lt_div_iff₀ h2e]; linarith
  have hδ1 : δ < 1 := by
    calc δ ≤ m / 10 ^ 16 := hspan
      _ < 2 ^ 53 / 10 ^ 16 := by gcongr
      _ < 1 := by norm_num
  unfold Near
  simp only
  have hB1 : ((B + 1 : ℕ) : ℚ) * 10 ^ (k - 16) / 2 ^ e = yB + δ := by
    rw [hyB, hδ]; push_cast; ring
  rw [hB1, ← hyB]
  split_ifs with hcond
  · -- just below a power of two the gap below is a quarter, but the spacing is below a half
    have hm52 : (m : ℚ) = 2 ^ 52 := by exact_mod_cast (hcond.1 : m = 2 ^ 52)
    have hδ2 : δ < 1 / 2 := by
      calc δ ≤ m / 10 ^ 16 := hspan
        _ = 2 ^ 52 / 10 ^ 16 := by rw [hm52]
        _ < 1 / 2 := by norm_num
    by_cases hnear : (m : ℚ) - yB < 1 / 4
    · left
      rcases eq_or_lt_of_le hy₁ with h | h
      · left; exact ⟨h.ge, Or.inl (by linarith)⟩
      · right; exact ⟨h, Or.inl hnear⟩
    · right; left; exact ⟨hy₂.le, Or.inl (by linarith)⟩
  · by_cases hnear : (m : ℚ) - yB < 1 / 2
    · left
      rcases eq_or_lt_of_le hy₁ with h | h
      · left; exact ⟨h.ge, Or.inl (by linarith)⟩
      · right; exact ⟨h, Or.inl hnear⟩
    · right; left; exact ⟨hy₂.le, Or.inl (by linarith)⟩

/-- The search loop returns digits that read back, provided it reaches seventeen digits. -/
theorem shortestDecimalAux_readsBack {m : ℕ} {e k : ℤ} (hc : Canonical .binary64 m e)
    (hk : (10 : ℚ) ^ k ≤ m * 2 ^ e) :
    ∀ (fuel p : ℕ), 1 ≤ p → p ≤ 17 → 17 - p < fuel →
      readsBack .binary64 m e (shortestDecimalAux .binary64 m e k fuel p).1
        (shortestDecimalAux .binary64 m e k fuel p).2 = true := by
  intro fuel
  induction fuel with
  | zero => intro p _ _ h; omega
  | succ n ih =>
    intro p hp₁ hp₂ hfuel
    simp only [shortestDecimalAux]
    cases h₁ : readsBack .binary64 m e (scaleFloor m e (-(k - ((p - 1 : ℕ) : ℤ))))
        (k - ((p - 1 : ℕ) : ℤ)) <;>
      cases h₂ : readsBack .binary64 m e (scaleFloor m e (-(k - ((p - 1 : ℕ) : ℤ))) + 1)
        (k - ((p - 1 : ℕ) : ℤ)) <;> simp only
    · -- neither reads back: below seventeen digits, try one more
      by_cases h17 : p = 17
      · subst h17
        have := seventeen_digits hc hk
        simp only [show (((17 - 1 : ℕ)) : ℤ) = 16 by norm_num] at h₁ h₂
        rw [h₁, h₂] at this; simp at this
      · exact ih (p + 1) (by omega) (by omega) (by omega)
    · exact h₂
    · exact h₁
    · split_ifs <;> assumption

/-- The printer's digits for a canonical `binary64` float always read back. -/
theorem shortestDecimal_readsBack {m : ℕ} {e : ℤ} (hc : Canonical .binary64 m e) (he : e ≤ 971) :
    readsBack .binary64 m e (shortestDecimal .binary64 m e).1
      (shortestDecimal .binary64 m e).2 = true :=
  shortestDecimalAux_readsBack hc (decimalExponent_binary64 hc he) _ 1 le_rfl (by norm_num)
    (by decide)

end FloatRoundtrip
