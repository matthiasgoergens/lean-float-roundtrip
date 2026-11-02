import FloatRoundtrip.Pack

/-!
# The round trip in the model

For every finite nonzero `Float.Model`, the digits and exponent that the printer writes read back,
through `Float.Model.ofScientific` and a negation for negative floats, to the same float.
-/

open Float.Model Float.Model.UnpackedFloat

namespace FloatRoundtrip

theorem stripTrailingZeros_value : ∀ (fuel c : ℕ) (q : ℤ),
    ((stripTrailingZeros fuel c q).1 : ℚ) * 10 ^ (stripTrailingZeros fuel c q).2 = c * 10 ^ q := by
  intro fuel
  induction fuel with
  | zero => intro c q; rfl
  | succ n ih =>
    intro c q
    simp only [stripTrailingZeros]
    split_ifs with h
    · rw [ih]
      obtain ⟨k, rfl⟩ : 10 ∣ c := Nat.dvd_of_mod_eq_zero h.1
      rw [Nat.mul_div_cancel_left _ (by norm_num), zpow_add₀ (by norm_num)]
      push_cast; ring
    · rfl

/-- A decimal near a float has nonzero digits. -/
theorem Near.digits_pos {spec : Format} {m c : ℕ} {e q : ℤ} (hm : 0 < m)
    (h : Near spec m e (c * 10 ^ q)) : 0 < c := by
  rcases Nat.eq_zero_or_pos c with rfl | hc
  · exfalso
    have hmQ : (1 : ℚ) ≤ m := by exact_mod_cast hm
    obtain ⟨h₁, -⟩ := near_bounds h
    simp only [Nat.cast_zero, zero_mul, zero_div] at h₁
    linarith
  · exact hc

/-- The digits and exponent the printer writes for the finite float `m * 2 ^ e`. -/
def printedDigits (m : ℕ) (e : ℤ) : ℕ × ℤ :=
  let d := shortestDecimal .binary64 m e
  stripTrailingZeros (Nat.log2 d.1 + 2) d.1 d.2

theorem printedDigits_near {m : ℕ} {e : ℤ} (hc : Canonical .binary64 m e) (he : e ≤ 971) :
    Near .binary64 m e ((printedDigits m e).1 * 10 ^ (printedDigits m e).2) := by
  have h := (readsBack_iff_near _ _ _ _ _).1 (shortestDecimal_readsBack hc he)
  unfold printedDigits
  simp only
  rw [stripTrailingZeros_value]
  exact h

theorem model_unpack_pack {s : Sign} {m : ℕ} {e : ℤ} {h : 0 < m} (hc : Canonical .binary64 m e)
    (he : e ≤ 971) : (Float.Model.pack (.finite s m e h)).unpack = .finite s m e h :=
  unpack_pack_finite hc he

/-- `ofScientific` reads a decimal near the canonical float `m * 2 ^ e` back as that float. -/
theorem modelOfScientific_of_near {m c : ℕ} {e q : ℤ} (hc : Canonical .binary64 m e)
    (he : e ≤ 971) (hn : Near .binary64 m e (c * 10 ^ q)) :
    Float.Model.ofScientific c q = Float.Model.pack (.finite .positive m e hc.1) := by
  unfold Float.Model.ofScientific
  rw [ofScientific_of_near (hn.digits_pos hc.1) hc (by simp; omega) (by decide) hn]

/--
**The round trip in the model.**  For every finite nonzero float `f`, reading back the digits and
exponent that the printer writes for it, and negating if `f` is negative, gives `f` again.
-/
theorem modelOfScientific_printedDigits (f : Float.Model) {s : Sign} {m : ℕ} {e : ℤ} {h : 0 < m}
    (hf : f.unpack = .finite s m e h) :
    (if s = .negative then
      -Float.Model.ofScientific (printedDigits m e).1 (printedDigits m e).2
    else Float.Model.ofScientific (printedDigits m e).1 (printedDigits m e).2) = f := by
  obtain ⟨hc, he⟩ := unpack_finite hf
  rw [modelOfScientific_of_near hc he (printedDigits_near hc he)]
  cases s with
  | positive =>
    simp only [reduceCtorEq, if_false]
    rw [← pack_unpack f, hf]
  | negative =>
    simp only [if_true]
    show Float.Model.pack (Float.Model.pack (.finite .positive m e hc.1)).unpack.neg = f
    rw [model_unpack_pack hc he, ← pack_unpack f, hf]
    rfl

end FloatRoundtrip
