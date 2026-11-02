import Mathlib

/-!
# Rounding in `Float.Model`

The model rounds every result through `roundWithAccuracy`, which shifts an `ExtendedMantissa`
(a mantissa with a round bit and a sticky bit) right one bit at a time and then rounds to nearest,
ties to even.  This file proves what that computes: an extended mantissa *describes* a rational
`x` when it holds `⌊x⌋` and the bits that locate `x` within the unit above it, each shift halves
the described value, and rounding a described value gives the nearest integer, ties to even.
-/

open Float.Model Float.Model.UnpackedFloat

namespace FloatRoundtrip

/--
`em` describes the rational `x`: its mantissa is `⌊x⌋`, its round bit says whether the fraction of
`x` is at least one half, and its sticky bit whether that fraction is neither zero nor one half.
-/
def Describes (em : ExtendedMantissa) (x : ℚ) : Prop :=
  (em.mantissa : ℚ) ≤ x ∧ x < em.mantissa + 1 ∧
  (em.roundBit = true ↔ (em.mantissa : ℚ) + 1 / 2 ≤ x) ∧
  (em.stickyBit = true ↔ x ≠ em.mantissa ∧ x ≠ em.mantissa + 1 / 2)

theorem describes_shiftRightOne {em : ExtendedMantissa} {x : ℚ} (h : Describes em x) :
    Describes em.shiftRightOne (x / 2) := by
  obtain ⟨M, rb, sb⟩ := em
  obtain ⟨h₁, h₂, hr, hs⟩ := h
  simp only at h₁ h₂ hr hs
  simp only [Describes, ExtendedMantissa.shiftRightOne, bne_iff_ne, ne_eq, Bool.or_eq_true]
  obtain ⟨a, rfl | rfl⟩ : ∃ a, M = 2 * a ∨ M = 2 * a + 1 := ⟨M / 2, by omega⟩
  · have hdiv : 2 * a / 2 = a := by omega
    have hmod : 2 * a % 2 = 0 := by omega
    rw [hdiv, hmod]
    push_cast at h₁ h₂ hr hs ⊢
    refine ⟨by linarith, by linarith, ?_, ?_⟩
    · simp only [not_true_eq_false, false_iff, not_le]; linarith
    · constructor
      · rintro (h | h)
        · have := hr.1 h; refine ⟨?_, ?_⟩ <;> intro <;> linarith
        · have := (hs.1 h).1; refine ⟨fun e => this (by linarith), fun e => by linarith⟩
      · rintro ⟨hne, -⟩
        by_cases hx : (2 * a : ℚ) + 1 / 2 ≤ x
        · exact Or.inl (hr.2 hx)
        · exact Or.inr (hs.2 ⟨fun e => hne (by linarith), fun e => hx (by linarith)⟩)
  · have hdiv : (2 * a + 1) / 2 = a := by omega
    have hmod : (2 * a + 1) % 2 = 1 := by omega
    rw [hdiv, hmod]
    push_cast at h₁ h₂ hr hs ⊢
    refine ⟨by linarith, by linarith, ?_, ?_⟩
    · simp only [ne_eq, one_ne_zero, not_false_eq_true, true_iff]; linarith
    · constructor
      · rintro (h | h)
        · have := hr.1 h; refine ⟨?_, ?_⟩ <;> intro <;> linarith
        · have := (hs.1 h).1; refine ⟨fun e => by linarith, fun e => this (by linarith)⟩
      · rintro ⟨-, hne⟩
        by_cases hx : (2 * a + 1 : ℚ) + 1 / 2 ≤ x
        · exact Or.inl (hr.2 hx)
        · exact Or.inr (hs.2 ⟨fun e => hne (by linarith), fun e => hx (by linarith)⟩)

theorem shiftRight_zero (em : ExtendedMantissa) : em >>> 0 = em := rfl

theorem shiftRight_succ (em : ExtendedMantissa) (n : ℕ) :
    em >>> (n + 1) = (em >>> n).shiftRightOne := rfl

theorem describes_shiftRight {em : ExtendedMantissa} {x : ℚ} (h : Describes em x) (n : ℕ) :
    Describes (em >>> n) (x / 2 ^ n) := by
  induction n with
  | zero => simp only [pow_zero, div_one]; exact h
  | succ n ih =>
    rw [shiftRight_succ, pow_succ, ← div_div]
    exact describes_shiftRightOne ih

/-- `R` is the integer nearest to `x`, the even one on a tie. -/
def IsRNE (x : ℚ) (R : ℕ) : Prop :=
  |x - R| < 1 / 2 ∨ (|x - R| = 1 / 2 ∧ R % 2 = 0)

theorem IsRNE.abs_le {x : ℚ} {R : ℕ} (h : IsRNE x R) : |x - R| ≤ 1 / 2 := by
  rcases h with h | ⟨h, -⟩
  · exact h.le
  · exact h.le

theorem IsRNE.even {x : ℚ} {R : ℕ} (h : IsRNE x R) (he : |x - R| = 1 / 2) : R % 2 = 0 := by
  rcases h with h | ⟨-, h⟩
  · rw [he] at h; exact absurd h (lt_irrefl _)
  · exact h

theorem IsRNE.unique {x : ℚ} {a b : ℕ} (ha : IsRNE x a) (hb : IsRNE x b) : a = b := by
  have key : ∀ {a b : ℕ}, IsRNE x a → IsRNE x b → a ≤ b := by
    intro a b ha hb
    by_contra hlt
    have hab : (b : ℚ) + 1 ≤ a := by exact_mod_cast (Nat.lt_of_not_le hlt)
    obtain ⟨ha₁, ha₂⟩ := _root_.abs_le.1 ha.abs_le
    obtain ⟨hb₁, hb₂⟩ := _root_.abs_le.1 hb.abs_le
    have hba : (a : ℚ) = b + 1 := by linarith
    have hea := ha.even (by rw [abs_eq (by norm_num)]; right; linarith)
    have heb := hb.even (by rw [abs_eq (by norm_num)]; left; linarith)
    have : a = b + 1 := by exact_mod_cast hba
    omega
  exact le_antisymm (key ha hb) (key hb ha)

theorem describes_roundedMantissa {em : ExtendedMantissa} {x : ℚ} (h : Describes em x) :
    IsRNE x em.roundedMantissa := by
  obtain ⟨M, rb, sb⟩ := em
  obtain ⟨h₁, h₂, hr, hs⟩ := h
  simp only at h₁ h₂ hr hs
  simp only [ExtendedMantissa.roundedMantissa, ExtendedMantissa.accuracy, IsRNE]
  cases rb <;> cases sb <;>
    simp only [Accuracy.roundToNearestEven, Bool.false_eq_true, false_iff, true_iff, not_le,
      not_and_or, not_not] at hr hs ⊢
  · -- exact
    rcases hs with hs | hs
    · left; rw [hs]; norm_num
    · exfalso; linarith
  · -- below the half
    left; rw [abs_lt]; constructor <;> linarith
  · -- on the half
    rcases hs with hs | hs
    · exfalso; linarith
    · right
      rcases Nat.mod_two_eq_zero_or_one M with hm | hm
      · rw [hm]; refine ⟨?_, by omega⟩; push_cast; rw [hs]; norm_num
      · rw [hm]; refine ⟨?_, by omega⟩; push_cast; rw [hs, abs_eq (by norm_num)]; right; ring
  · -- above the half
    have : (M : ℚ) + 1 / 2 < x := lt_of_le_of_ne hr (Ne.symm hs.2)
    left; push_cast; rw [abs_lt]; constructor <;> linarith

end FloatRoundtrip

/-! ## Landing on a given float -/

namespace FloatRoundtrip

/--
The rational `r` is within the rounding interval of the float `m * 2 ^ e` in `spec`: measured in
units of `2 ^ e`, less than half a unit above it and less than half a unit below it (a quarter
just below a power of two, where the next smaller float is closer), with the boundaries included
when `m` is even.
-/
def Near (spec : Format) (m : ℕ) (e : ℤ) (r : ℚ) : Prop :=
  let y := r / 2 ^ e
  let hb : ℚ :=
    if m = 2 ^ spec.mantissaBitsWithoutImplicit ∧ e > spec.minExponent then 1 / 4 else 1 / 2
  ((m : ℚ) ≤ y ∧ (y - m < 1 / 2 ∨ (y - m = 1 / 2 ∧ m % 2 = 0))) ∨
    (y < m ∧ (m - y < hb ∨ (m - y = hb ∧ m % 2 = 0)))

/-- The float `m * 2 ^ e` is in the canonical form of `spec` that `unpack` produces. -/
def Canonical (spec : Format) (m : ℕ) (e : ℤ) : Prop :=
  0 < m ∧ e = spec.targetExponent (totalExponent m e)

theorem two_zpow_log2_le {M : ℕ} (hM : M ≠ 0) : (2 : ℚ) ^ (M.log2 : ℤ) ≤ M := by
  rw [zpow_natCast]; exact_mod_cast Nat.log2_self_le hM

theorem succ_le_two_zpow_log2 (M : ℕ) : (M : ℚ) + 1 ≤ 2 ^ ((M.log2 : ℤ) + 1) := by
  rw [show ((M.log2 : ℤ) + 1) = ((M.log2 + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast]
  exact_mod_cast Nat.lt_log2_self

theorem near_bounds {spec : Format} {m : ℕ} {e : ℤ} {r : ℚ} (h : Near spec m e r) :
    (m : ℚ) - 1 / 2 ≤ r / 2 ^ e ∧ r / 2 ^ e ≤ m + 1 / 2 := by
  simp only [Near] at h
  split_ifs at h <;> rcases h with ⟨h₁, h₂ | ⟨h₂, -⟩⟩ | ⟨h₁, h₂ | ⟨h₂, -⟩⟩ <;>
    constructor <;> linarith

theorem lt_of_zpow_le_lt {a b : ℤ} {r : ℚ} (h₁ : (2 : ℚ) ^ a ≤ r) (h₂ : r < 2 ^ b) : a < b :=
  (zpow_lt_zpow_iff_right₀ one_lt_two).1 (lt_of_le_of_lt h₁ h₂)

/--
Where the first shift of `roundWithAccuracy` goes, for a value near the canonical float
`m * 2 ^ e`: to `e`, or to `e - 1` when the value lies just below the power of two `m * 2 ^ e`.
-/
theorem target_cases {spec : Format} {M : ℕ} {E : ℤ} {x : ℚ} (hx₁ : (M : ℚ) ≤ x)
    (hx₂ : x < M + 1) (hE : E ≤ spec.targetExponent (totalExponent M E))
    {m : ℕ} {e : ℤ} (hc : Canonical spec m e) (hn : Near spec m e (x * 2 ^ E)) :
    spec.targetExponent (totalExponent M E) = e ∨
      (spec.targetExponent (totalExponent M E) = e - 1 ∧
        m = 2 ^ spec.mantissaBitsWithoutImplicit ∧ e > spec.minExponent ∧
        x * 2 ^ E / 2 ^ e < m) := by
  obtain ⟨hm, hce⟩ := hc
  have hmw := spec.hm
  have hmb : spec.mantissaBits = 1 + spec.mantissaBitsWithoutImplicit := rfl
  set r := x * 2 ^ E with hr_def
  obtain ⟨hy₁, hy₂⟩ := near_bounds hn
  have h2e : (0 : ℚ) < 2 ^ e := zpow_pos two_pos e
  have h2E : (0 : ℚ) < 2 ^ E := zpow_pos two_pos E
  have hr : r = r / 2 ^ e * 2 ^ e := by field_simp
  have hmQ : (1 : ℚ) ≤ m := by exact_mod_cast hm
  have hlogm := two_zpow_log2_le (Nat.pos_iff_ne_zero.1 hm)
  have hlogm' := succ_le_two_zpow_log2 m
  -- the binade of `m * 2 ^ e` bounds the binade of `r`
  have hB₁ : r < 2 ^ ((m.log2 : ℤ) + 1 + e) := by
    rw [zpow_add₀ two_ne_zero]
    calc r = r / 2 ^ e * 2 ^ e := hr
      _ ≤ (m + 1 / 2) * 2 ^ e := by gcongr
      _ < (m + 1) * 2 ^ e := by gcongr; norm_num
      _ ≤ 2 ^ ((m.log2 : ℤ) + 1) * 2 ^ e := by gcongr
  have hB₂ : (2 : ℚ) ^ ((m.log2 : ℤ) + 1 + e - 2) ≤ r := by
    rw [show (m.log2 : ℤ) + 1 + e - 2 = (m.log2 : ℤ) + e + (-1) by ring,
      zpow_add₀ two_ne_zero, zpow_add₀ two_ne_zero, zpow_neg_one]
    calc (2 : ℚ) ^ (m.log2 : ℤ) * 2 ^ e * 2⁻¹ ≤ m * 2 ^ e * 2⁻¹ := by gcongr
      _ ≤ (m - 1 / 2) * 2 ^ e := by nlinarith
      _ ≤ r / 2 ^ e * 2 ^ e := by gcongr
      _ = r := hr.symm
  simp only [Format.targetExponent, totalExponent] at hE hce ⊢
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · -- `x < 1`, so the value is below `2 ^ E`, which forces the subnormal range
    have hrE : r < 2 ^ E := by
      calc r = x * 2 ^ E := rfl
        _ < 1 * 2 ^ E := by gcongr; simpa using hx₂
        _ = 2 ^ E := one_mul _
    have := lt_of_zpow_le_lt hB₂ hrE
    simp only [Nat.log2_zero, Nat.cast_zero, zero_add] at hE ⊢
    left; omega
  · have hMQ : (1 : ℚ) ≤ M := by exact_mod_cast hM
    have hlogM := two_zpow_log2_le (Nat.pos_iff_ne_zero.1 hM)
    have hlogM' := succ_le_two_zpow_log2 M
    have hA₁ : (2 : ℚ) ^ ((M.log2 : ℤ) + 1 + E - 1) ≤ r := by
      rw [show (M.log2 : ℤ) + 1 + E - 1 = (M.log2 : ℤ) + E by ring, zpow_add₀ two_ne_zero]
      calc (2 : ℚ) ^ (M.log2 : ℤ) * 2 ^ E ≤ M * 2 ^ E := by gcongr
        _ ≤ x * 2 ^ E := by gcongr
    have hA₂ : r < 2 ^ ((M.log2 : ℤ) + 1 + E) := by
      rw [zpow_add₀ two_ne_zero]
      calc r = x * 2 ^ E := rfl
        _ < (M + 1) * 2 ^ E := by gcongr
        _ ≤ 2 ^ ((M.log2 : ℤ) + 1) * 2 ^ E := by gcongr
    have h₁ := lt_of_zpow_le_lt hA₁ hB₁
    have h₂ := lt_of_zpow_le_lt hB₂ hA₂
    by_cases hAB : (M.log2 : ℤ) + 1 + E = (m.log2 : ℤ) + 1 + e
    · left; rw [hAB]; omega
    · -- one binade lower: `r` is below the power of two `2 ^ (log2 m + e) ≤ m * 2 ^ e`
      have hAB' : (M.log2 : ℤ) + 1 + E = (m.log2 : ℤ) + e := by omega
      have hrP : r / 2 ^ e < 2 ^ (m.log2 : ℤ) := by
        rw [div_lt_iff₀ h2e, ← zpow_add₀ two_ne_zero, ← hAB']; exact hA₂
      by_cases hmin : e > spec.minExponent
      · have hlog : m.log2 + 1 = spec.mantissaBits := by omega
        -- `m - 1/2 ≤ r / 2^e < 2 ^ log2 m ≤ m` pins `m` to the power of two
        have hpow : m = 2 ^ m.log2 := by
          have hle : 2 ^ m.log2 ≤ m := Nat.log2_self_le (Nat.pos_iff_ne_zero.1 hm)
          have hlt : (m : ℚ) < 2 ^ m.log2 + 1 := by
            have := lt_of_le_of_lt hy₁ hrP
            rw [zpow_natCast] at this; linarith
          have : m < 2 ^ m.log2 + 1 := by exact_mod_cast hlt
          omega
        right
        refine ⟨by omega, ?_, hmin, by linarith⟩
        rw [hpow]; congr 1; omega
      · left; omega

/-- `roundWithAccuracy` with its pattern-matching `let`s spelled out. -/
theorem roundWithAccuracy_eq (spec : Format) (s : Sign) (M : ℕ) (E : ℤ) (acc : Accuracy) :
    roundWithAccuracy spec s M E acc =
      let sh₁ := (spec.targetExponent (totalExponent M E) - E).toNat
      let R := (ExtendedMantissa.ofMantissaAndAccuracy M acc >>> sh₁).roundedMantissa
      let e₁ := E + sh₁
      let sh₂ := (spec.targetExponent (totalExponent R e₁) - e₁).toNat
      let fm := (ExtendedMantissa.ofMantissaAndAccuracy R .exact >>> sh₂).mantissa
      if h : fm = 0 then .zero s else .finite s fm (e₁ + sh₂) (Nat.pos_of_ne_zero h) := rfl

theorem mantissa_ofMantissaAndAccuracy (M : ℕ) (acc : Accuracy) :
    (ExtendedMantissa.ofMantissaAndAccuracy M acc).mantissa = M := by
  cases acc with
  | exact => rfl
  | inexact o => cases o <;> rfl

theorem near_isRNE {spec : Format} {m : ℕ} {e : ℤ} {r : ℚ} (h : Near spec m e r) :
    IsRNE (r / 2 ^ e) m := by
  simp only [Near] at h
  unfold IsRNE
  split_ifs at h <;> rcases h with ⟨h₁, h₂ | ⟨h₂, hev⟩⟩ | ⟨h₁, h₂ | ⟨h₂, hev⟩⟩
  all_goals first
    | (left; rw [abs_lt]; constructor <;> linarith)
    | (right; refine ⟨?_, hev⟩; rw [abs_eq (by norm_num)]; first | (left; linarith) | (right; linarith))

theorem near_isRNE_below {spec : Format} {m : ℕ} {e : ℤ} {r : ℚ} (h : Near spec m e r)
    (hpow : m = 2 ^ spec.mantissaBitsWithoutImplicit) (hmin : e > spec.minExponent)
    (hlt : r / 2 ^ e < m) : IsRNE (r / 2 ^ (e - 1)) (2 * m) := by
  simp only [Near, hpow, hmin, and_self, ite_true] at h
  rw [← hpow] at h
  have hy : r / 2 ^ (e - 1) = 2 * (r / 2 ^ e) := by
    rw [zpow_sub₀ two_ne_zero, zpow_one]; field_simp
  rw [hy]
  unfold IsRNE
  rcases h with ⟨h₁, -⟩ | ⟨-, h₂ | ⟨h₂, -⟩⟩
  · exfalso; linarith
  · left; push_cast; rw [abs_lt]; constructor <;> linarith
  · right; push_cast; refine ⟨?_, by omega⟩; rw [abs_eq (by norm_num)]; right; linarith

/--
`roundWithAccuracy` lands on the canonical float `m * 2 ^ e` when the value it rounds is near it.
The value is described by the mantissa `M` and the accuracy `acc` at exponent `E`, and `E` must not
be above the first shift's target, so that the rounding only shifts right.
-/
theorem roundWithAccuracy_of_near {spec : Format} (s : Sign) {M : ℕ} {E : ℤ} {acc : Accuracy}
    {x : ℚ} (hx : Describes (.ofMantissaAndAccuracy M acc) x)
    (hE : E ≤ spec.targetExponent (totalExponent M E))
    {m : ℕ} {e : ℤ} (hc : Canonical spec m e) (hn : Near spec m e (x * 2 ^ E)) :
    roundWithAccuracy spec s M E acc = .finite s m e hc.1 := by
  have hx₁ := hx.1
  have hx₂ := hx.2.1
  rw [mantissa_ofMantissaAndAccuracy] at hx₁ hx₂
  have hsh : (((spec.targetExponent (totalExponent M E) - E).toNat : ℕ) : ℤ) =
      spec.targetExponent (totalExponent M E) - E := Int.toNat_of_nonneg (by omega)
  have hd := describes_shiftRight hx (spec.targetExponent (totalExponent M E) - E).toNat
  have hval : x / 2 ^ (spec.targetExponent (totalExponent M E) - E).toNat =
      x * 2 ^ E / 2 ^ spec.targetExponent (totalExponent M E) := by
    rw [← zpow_natCast, hsh, zpow_sub₀ two_ne_zero]; field_simp
  rw [hval] at hd
  have hR := describes_roundedMantissa hd
  have hm := hc.1
  rw [roundWithAccuracy_eq]
  simp only
  rcases target_cases hx₁ hx₂ hE hc hn with h | ⟨h, hpow, hmin, hlt⟩
  · rw [hR.unique (by rw [h]; exact near_isRNE hn)]
    have he₁ : E + (((spec.targetExponent (totalExponent M E) - E).toNat : ℕ) : ℤ) = e := by
      omega
    have hsh₂ : (spec.targetExponent (totalExponent m e) - e).toNat = 0 := by
      have := hc.2; omega
    simp only [he₁, hsh₂, shiftRight_zero, mantissa_ofMantissaAndAccuracy]
    split_ifs with h0
    · exact absurd h0 (by omega)
    · simp
  · rw [hR.unique (by rw [h]; exact near_isRNE_below hn hpow hmin hlt)]
    have he₁ : E + (((spec.targetExponent (totalExponent M E) - E).toNat : ℕ) : ℤ) = e - 1 := by
      omega
    have hlog : (2 * m).log2 = m.log2 + 1 := by
      exact Nat.log2_two_mul (by omega)
    have hte : totalExponent (2 * m) (e - 1) = totalExponent m e := by
      simp only [totalExponent, hlog]; push_cast; ring
    have hsh₂ : (spec.targetExponent (totalExponent (2 * m) (e - 1)) - (e - 1)).toNat = 1 := by
      rw [hte]; have := hc.2; omega
    simp only [he₁, hsh₂]
    have hfm : (ExtendedMantissa.ofMantissaAndAccuracy (2 * m) .exact >>> 1).mantissa = m := by
      show (2 * m) / 2 = m; omega
    simp only [hfm]
    split_ifs with h0
    · exact absurd h0 (by omega)
    · congr 1; push_cast; ring

end FloatRoundtrip
