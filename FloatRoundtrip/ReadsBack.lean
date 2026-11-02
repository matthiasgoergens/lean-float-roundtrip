import FloatRoundtrip.Print
import FloatRoundtrip.Parse

/-!
# The printer's acceptance test

`readsBack` decides whether `c * 10 ^ q` reads back to the float `m * 2 ^ e` by comparing natural
numbers, all scaled by `2 ^ t * 10 ^ s` so that no fractions arise.  This file shows that it decides
exactly `Near`.
-/

open Float.Model Float.Model.UnpackedFloat

namespace FloatRoundtrip

/-- The comparisons `readsBack` makes on natural numbers, read in `ℚ`. -/
theorem readsBack_core (V C HA HB : ℕ) (inc : Prop) [Decidable inc] :
    (if V ≤ C then (if inc then decide (C - V ≤ HA) else decide (C - V < HA))
      else (if inc then decide (V - C ≤ HB) else decide (V - C < HB))) = true ↔
    (((V : ℚ) ≤ C ∧ ((C : ℚ) - V < HA ∨ ((C : ℚ) - V = HA ∧ inc))) ∨
      ((C : ℚ) < V ∧ ((V : ℚ) - C < HB ∨ ((V : ℚ) - C = HB ∧ inc)))) := by
  by_cases hVC : V ≤ C
  · have hVCQ : (V : ℚ) ≤ C := by exact_mod_cast hVC
    have hsub : ((C - V : ℕ) : ℚ) = C - V := Nat.cast_sub hVC
    have hnot : ¬ (C : ℚ) < V := not_lt.2 hVCQ
    simp only [hVC, ite_true, hVCQ, true_and, hnot, false_and, or_false]
    by_cases hinc : inc
    · simp only [hinc, ite_true, decide_eq_true_eq, and_true]
      rw [← hsub, Nat.cast_lt, Nat.cast_inj]; exact le_iff_lt_or_eq
    · simp only [hinc, ite_false, decide_eq_true_eq, and_false, or_false]
      rw [← hsub]; exact_mod_cast Iff.rfl
  · have hCV : C < V := Nat.lt_of_not_le hVC
    have hCVQ : (C : ℚ) < V := by exact_mod_cast hCV
    have hsub : ((V - C : ℕ) : ℚ) = V - C := Nat.cast_sub hCV.le
    have hnot : ¬ (V : ℚ) ≤ C := not_le.2 hCVQ
    simp only [hVC, ite_false, hCVQ, true_and, hnot, false_and, false_or]
    by_cases hinc : inc
    · simp only [hinc, ite_true, decide_eq_true_eq, and_true]
      rw [← hsub, Nat.cast_lt, Nat.cast_inj]; exact le_iff_lt_or_eq
    · simp only [hinc, ite_false, decide_eq_true_eq, and_false, or_false]
      rw [← hsub]; exact_mod_cast Iff.rfl

/-- `readsBack` decides `Near`. -/
theorem readsBack_iff_near (spec : Format) (m : ℕ) (e : ℤ) (c : ℕ) (q : ℤ) :
    readsBack spec m e c q = true ↔ Near spec m e (c * 10 ^ q) := by
  unfold readsBack scaledAround
  simp only
  rw [readsBack_core]
  set t := (2 - e).toNat with ht
  set s := (-q).toNat with hs
  set e2 := (e + t).toNat with he2
  have he2' : (e2 : ℤ) = e + t := by omega
  have he2two : 2 ≤ e2 := by omega
  have hqs : ((q + s).toNat : ℤ) = q + s := by omega
  set L : ℚ := 2 ^ e * 2 ^ t * 10 ^ s with hL
  have hLpos : 0 < L := by positivity
  set y : ℚ := c * 10 ^ q / 2 ^ e with hy
  have h2e : (0 : ℚ) < 2 ^ e := zpow_pos two_pos e
  have hV : ((m * 2 ^ e2 * 10 ^ s : ℕ) : ℚ) = m * L := by
    push_cast
    rw [← zpow_natCast (2 : ℚ) e2, he2', zpow_add₀ two_ne_zero, zpow_natCast]; ring
  have hC : ((c * 10 ^ (q + s).toNat * 2 ^ t : ℕ) : ℚ) = y * L := by
    push_cast
    rw [← zpow_natCast (10 : ℚ) (q + s).toNat, hqs, zpow_add₀ (by norm_num), zpow_natCast, hy, hL]
    field_simp
  have hHA : ((2 ^ (e2 - 1) * 10 ^ s : ℕ) : ℚ) = 1 / 2 * L := by
    push_cast
    rw [← zpow_natCast (2 : ℚ) (e2 - 1), show (((e2 - 1 : ℕ)) : ℤ) = e + t + (-1) by omega,
      zpow_add₀ two_ne_zero, zpow_add₀ two_ne_zero, zpow_natCast, zpow_neg_one]; ring
  have hHB : ((2 ^ (e2 - 2) * 10 ^ s : ℕ) : ℚ) = 1 / 4 * L := by
    push_cast
    rw [← zpow_natCast (2 : ℚ) (e2 - 2), show (((e2 - 2 : ℕ)) : ℤ) = e + t + (-2) by omega,
      zpow_add₀ two_ne_zero, zpow_add₀ two_ne_zero, zpow_natCast, zpow_neg, zpow_two]; ring
  have hlt : ∀ a b k : ℚ, b * L - a * L < k * L ↔ b - a < k := fun a b k => by
    rw [← sub_mul]; exact mul_lt_mul_iff_of_pos_right hLpos
  have heq : ∀ a b k : ℚ, b * L - a * L = k * L ↔ b - a = k := fun a b k => by
    rw [← sub_mul]; exact mul_left_inj' hLpos.ne'
  unfold Near
  simp only
  rw [← hy, hV, hC, hHA]
  by_cases hcond : m = 2 ^ spec.mantissaBitsWithoutImplicit ∧ e > spec.minExponent
  · rw [if_pos hcond, if_pos hcond, hHB]
    simp only [hlt, heq]
    rw [mul_le_mul_iff_of_pos_right hLpos, mul_lt_mul_iff_of_pos_right hLpos]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hcond), ite_eq_right_of_eq_false _ _ (eq_false hcond), hHA]
    simp only [hlt, heq]
    rw [mul_le_mul_iff_of_pos_right hLpos, mul_lt_mul_iff_of_pos_right hLpos]

end FloatRoundtrip
