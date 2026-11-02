import FloatRoundtrip.Shortest

/-!
# Packing and unpacking `binary64`

`Float.Model` stores the 64 bits of a float, and every operation goes through `unpack` and `pack`.
This file shows that `unpack` produces canonical floats within the `binary64` exponent range, that
`pack ∘ unpack` is the identity on valid bit patterns, and that `unpack ∘ pack` is the identity on
canonical floats in range.
-/

open Float.Model Float.Model.UnpackedFloat

namespace FloatRoundtrip

@[simp] theorem binary64_mantissaBitsWithoutImplicit :
    Format.binary64.mantissaBitsWithoutImplicit = 52 := rfl
@[simp] theorem binary64_exponentBits : Format.binary64.exponentBits = 11 := rfl
@[simp] theorem binary64_mantissaBits : Format.binary64.mantissaBits = 53 := rfl
@[simp] theorem binary64_exponentBias : Format.binary64.exponentBias = 1023 := rfl

theorem minusOne_toNat : (-1#11 : BitVec 11).toNat = 2047 := rfl

theorem log2_eq_of_bounds {m k : ℕ} (h₁ : 2 ^ k ≤ m) (h₂ : m < 2 ^ (k + 1)) : m.log2 = k := by
  have hm : m ≠ 0 := by have := Nat.one_le_two_pow (n := k); omega
  have := (Nat.le_log2 hm).2 h₁
  have := (Nat.log2_lt hm).2 h₂
  omega

/-- The finite floats `unpack` produces are canonical, with exponents at most `971`. -/
theorem unpack_finite {b : BitVec 64} {s : Sign} {m : ℕ} {e : ℤ} {h : 0 < m}
    (hu : UnpackedFloat.unpack .binary64 b = .finite s m e h) :
    Canonical .binary64 m e ∧ e ≤ 971 := by
  unfold UnpackedFloat.unpack at hu
  simp only at hu
  have hev := (unpackExponent (spec := .binary64) b).isLt
  have hmv := (unpackMantissa (spec := .binary64) b).isLt
  simp only [binary64_exponentBits, binary64_mantissaBitsWithoutImplicit] at hev hmv
  by_cases h₁ : unpackExponent (spec := .binary64) b = -1#_
  · simp only [h₁, ite_true] at hu; split_ifs at hu
  simp only [h₁, ite_false] at hu
  by_cases h₂ : unpackExponent (spec := .binary64) b = 0#_
  · simp only [h₂, ite_true] at hu
    split_ifs at hu
    -- subnormal
    injection hu with hs hm he
    subst hm he
    have hlog : (unpackMantissa (spec := .binary64) b).toNat.log2 < 52 :=
      (Nat.log2_lt (by omega)).2 hmv
    refine ⟨⟨h, ?_⟩, ?_⟩
    · simp only [Format.targetExponent, totalExponent, binary64_minExponent,
        binary64_exponentBias, binary64_mantissaBits, BitVec.toNat_ofNat, Nat.zero_mod]
      omega
    · simp only [binary64_exponentBias, BitVec.toNat_ofNat, Nat.zero_mod]; omega
  · -- normal
    simp only [h₂, ite_false] at hu
    injection hu with hs hm he
    subst hm he
    have hne1 : (unpackExponent (spec := .binary64) b).toNat ≠ 2047 := fun h =>
      h₁ (BitVec.eq_of_toNat_eq (by rw [h]; rfl))
    have hne0 : (unpackExponent (spec := .binary64) b).toNat ≠ 0 := fun h =>
      h₂ (BitVec.eq_of_toNat_eq (by rw [h]; rfl))
    have hmant : (1#1 ++ unpackMantissa (spec := .binary64) b).toNat =
        2 ^ 52 + (unpackMantissa (spec := .binary64) b).toNat := by
      rw [BitVec.toNat_append]
      simp only [binary64_mantissaBitsWithoutImplicit, BitVec.toNat_ofNat]
      rw [← Nat.shiftLeft_add_eq_or_of_lt hmv]; simp [Nat.shiftLeft_eq]
    have hlog : (1#1 ++ unpackMantissa (spec := .binary64) b).toNat.log2 = 52 := by
      rw [hmant]; exact log2_eq_of_bounds (by omega) (by omega)
    refine ⟨⟨by simp, ?_⟩, ?_⟩
    · simp only [Format.targetExponent, totalExponent, binary64_minExponent, hlog,
        binary64_exponentBias, binary64_mantissaBits]
      omega
    · simp only [binary64_exponentBias]; omega

theorem toNat_fields (x : BitVec 1) (y : BitVec 11) (z : BitVec 52) :
    (x ++ y ++ z).toNat = x.toNat * 2 ^ 63 + y.toNat * 2 ^ 52 + z.toNat := by
  rw [BitVec.toNat_append, BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt z.isLt,
    ← Nat.shiftLeft_add_eq_or_of_lt y.isLt]
  simp only [Nat.shiftLeft_eq]; ring

theorem unpack_fields (x : BitVec 1) (y : BitVec 11) (z : BitVec 52) :
    unpackSign (spec := .binary64) (x ++ y ++ z) = x ∧
      unpackExponent (spec := .binary64) (x ++ y ++ z) = y ∧
      unpackMantissa (spec := .binary64) (x ++ y ++ z) = z := by
  have hx := x.isLt; have hy := y.isLt; have hz := z.isLt
  have h := toNat_fields x y z
  refine ⟨BitVec.eq_of_toNat_eq ?_, BitVec.eq_of_toNat_eq ?_, BitVec.eq_of_toNat_eq ?_⟩ <;>
    simp only [unpackSign, unpackExponent, unpackMantissa, BitVec.extractLsb'_toNat,
      binary64_exponentBits, binary64_mantissaBitsWithoutImplicit, Nat.shiftRight_eq_div_pow] <;>
    rw [h] <;> omega

theorem fields_eq (b : BitVec 64) :
    unpackSign (spec := .binary64) b ++ unpackExponent (spec := .binary64) b ++
      unpackMantissa (spec := .binary64) b = b := by
  apply BitVec.eq_of_toNat_eq
  rw [toNat_fields]
  have hb := b.isLt
  simp only [unpackSign, unpackExponent, unpackMantissa, BitVec.extractLsb'_toNat,
    binary64_exponentBits, binary64_mantissaBitsWithoutImplicit, Nat.shiftRight_eq_div_pow]
  omega

theorem sign_ofBitVec_toBitVec (s : Sign) : Sign.ofBitVec s.toBitVec = s := by
  cases s <;> rfl

theorem sign_toBitVec_ofBitVec (x : BitVec 1) : (Sign.ofBitVec x).toBitVec = x := by
  have h : x.toNat = 0 ∨ x.toNat = 1 := by have := x.isLt; omega
  rcases h with h | h
  · obtain rfl : x = 0#1 := BitVec.eq_of_toNat_eq h; rfl
  · obtain rfl : x = 1#1 := BitVec.eq_of_toNat_eq h; rfl

theorem toNat_one_append (z : BitVec 52) : (1#1 ++ z).toNat = 2 ^ 52 + z.toNat := by
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt z.isLt]; simp [Nat.shiftLeft_eq]

/-- `unpack ∘ pack` is the identity on canonical finite floats in the `binary64` range. -/
theorem unpack_pack_finite {s : Sign} {m : ℕ} {e : ℤ} {h : 0 < m} (hc : Canonical .binary64 m e)
    (he : e ≤ 971) :
    UnpackedFloat.unpack .binary64 (UnpackedFloat.pack .binary64 (.finite s m e h)) =
      .finite s m e h := by
  have hmlt : m < 2 ^ 53 := hc.lt_two_pow
  have hmin : -1074 ≤ e := binary64_minExponent ▸ hc.minExponent_le
  have hce := hc.2
  simp only [Format.targetExponent, totalExponent, binary64_minExponent,
    binary64_mantissaBits] at hce
  have hlog : m.log2 < 53 := (Nat.log2_lt h.ne').2 hmlt
  unfold UnpackedFloat.pack packComponents
  dsimp only
  split_ifs with hb hm'
  · -- overflow to infinity cannot happen below exponent 971
    simp only [binary64_exponentBias, binary64_mantissaBitsWithoutImplicit, binary64_exponentBits,
      Nat.cast_ofNat] at hb
    omega
  · -- normal: the biased exponent is in `[1, 2046]`
    simp only [binary64_mantissaBits] at hm'
    have hm52 : 2 ^ 52 ≤ m := by
      have := Nat.log2_self_le h.ne'; rw [show m.log2 = 52 by omega] at this; exact this
    simp only [binary64_exponentBias, binary64_mantissaBitsWithoutImplicit, binary64_exponentBits,
      Nat.cast_ofNat]
    obtain ⟨hs, hy, hz⟩ := unpack_fields s.toBitVec (BitVec.ofNat 11 (e + 1023 + 52).toNat)
      (BitVec.ofNat 52 m)
    unfold UnpackedFloat.unpack
    simp only [hs, hy, hz, sign_ofBitVec_toBitVec]
    have hev : (BitVec.ofNat 11 (e + 1023 + 52).toNat).toNat = (e + 1023 + 52).toNat := by
      rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
    rw [if_neg (fun h' => by have := congrArg BitVec.toNat h'; rw [hev, minusOne_toNat] at this; omega),
      if_neg (fun h' => by have := congrArg BitVec.toNat h'; rw [hev] at this; simp at this; omega)]
    congr 1
    · rw [toNat_one_append, BitVec.toNat_ofNat]; omega
    · simp only [binary64_exponentBias, binary64_mantissaBitsWithoutImplicit, hev]; omega
  · -- subnormal: the exponent is the minimum, the mantissa below `2 ^ 52`
    simp only [binary64_mantissaBits] at hm'
    have hlog' : m.log2 < 52 := by omega
    have he' : e = -1074 := by omega
    have hmlt' : m < 2 ^ 52 := by
      calc m < 2 ^ (m.log2 + 1) := Nat.lt_log2_self
        _ ≤ 2 ^ 52 := Nat.pow_le_pow_right (by norm_num) (by omega)
    try simp only [binary64_mantissaBitsWithoutImplicit, binary64_exponentBits]
    obtain ⟨hs, hy, hz⟩ := unpack_fields s.toBitVec 0#11 (BitVec.ofNat 52 m)
    unfold UnpackedFloat.unpack
    simp only [hs, hy, hz, sign_ofBitVec_toBitVec]
    have hmz : (BitVec.ofNat 52 m).toNat = m := by rw [BitVec.toNat_ofNat]; omega
    rw [if_neg (by decide), if_pos trivial, dif_neg (fun h' => by
      have := congrArg BitVec.toNat h'; rw [hmz] at this; simp at this; omega)]
    congr 1
    all_goals first
      | exact hmz
      | (simp only [binary64_exponentBias, binary64_mantissaBitsWithoutImplicit, BitVec.toNat_ofNat,
          Nat.zero_mod]; omega)

theorem unpack_pack_zero (s : Sign) :
    UnpackedFloat.unpack .binary64 (UnpackedFloat.pack .binary64 (.zero s)) = .zero s := by
  unfold UnpackedFloat.pack packedZero packComponents
  obtain ⟨hs, hy, hz⟩ := unpack_fields s.toBitVec (0 : BitVec 11) (0 : BitVec 52)
  unfold UnpackedFloat.unpack
  simp only [hs, hy, hz, sign_ofBitVec_toBitVec]
  rfl

theorem ofNat_toNat_self {n : ℕ} (x : BitVec n) : BitVec.ofNat n x.toNat = x :=
  BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt x.isLt])

/-- `pack ∘ unpack` is the identity on valid `binary64` bit patterns. -/
theorem pack_unpack_bits (b : BitVec 64) (hv : Format.binary64.Valid b) :
    UnpackedFloat.pack .binary64 (UnpackedFloat.unpack .binary64 b) = b := by
  have hb := fields_eq b
  have hyl := (unpackExponent (spec := .binary64) b).isLt
  have hzl := (unpackMantissa (spec := .binary64) b).isLt
  simp only [binary64_exponentBits, binary64_mantissaBitsWithoutImplicit] at hyl hzl
  unfold UnpackedFloat.unpack
  dsimp only
  by_cases h₁ : unpackExponent (spec := .binary64) b = -1#_
  · rw [if_pos h₁]
    by_cases h₂ : unpackMantissa (spec := .binary64) b = 0#_
    · -- infinity
      rw [if_pos h₂]
      unfold UnpackedFloat.pack packedInfinity packComponents
      rw [sign_toBitVec_ofBitVec, ← h₁, show (0 : BitVec 52) = 0#52 from rfl, ← h₂]; exact hb
    · -- NaN, which `Valid` makes canonical
      rw [if_neg h₂]
      exact (hv.eq_packedNaN h₁ h₂).symm
  · rw [if_neg h₁]
    have hne1 : (unpackExponent (spec := .binary64) b).toNat ≠ 2047 := fun h =>
      h₁ (BitVec.eq_of_toNat_eq (by rw [h]; rfl))
    by_cases h₃ : unpackExponent (spec := .binary64) b = 0#_
    · rw [if_pos h₃]
      have hy0 : (unpackExponent (spec := .binary64) b).toNat = 0 := by rw [h₃]; rfl
      by_cases h₄ : unpackMantissa (spec := .binary64) b = 0#_
      · -- zero
        rw [dif_pos h₄]
        unfold UnpackedFloat.pack packedZero packComponents
        rw [sign_toBitVec_ofBitVec, show (0 : BitVec 11) = 0#11 from rfl, ← h₃,
          show (0 : BitVec 52) = 0#52 from rfl, ← h₄]; exact hb
      · -- subnormal
        rw [dif_neg h₄]
        have hz0 : (unpackMantissa (spec := .binary64) b).toNat ≠ 0 := fun h =>
          h₄ (BitVec.eq_of_toNat_eq (by rw [h]; rfl))
        have hlog : (unpackMantissa (spec := .binary64) b).toNat.log2 < 52 :=
          (Nat.log2_lt hz0).2 hzl
        unfold UnpackedFloat.pack packComponents
        dsimp only
        simp only [binary64_exponentBias, binary64_mantissaBitsWithoutImplicit,
          binary64_exponentBits, binary64_mantissaBits, Nat.cast_ofNat, hy0]
        split_ifs <;> try omega
        rw [sign_toBitVec_ofBitVec, ofNat_toNat_self, ← h₃]; exact hb
    · -- normal
      rw [if_neg h₃]
      have hy0 : (unpackExponent (spec := .binary64) b).toNat ≠ 0 := fun h =>
        h₃ (BitVec.eq_of_toNat_eq (by rw [h]; rfl))
      have hlog : (1#1 ++ unpackMantissa (spec := .binary64) b).toNat.log2 = 52 := by
        rw [toNat_one_append]; exact log2_eq_of_bounds (by omega) (by omega)
      unfold UnpackedFloat.pack packComponents
      dsimp only
      simp only [binary64_exponentBias, binary64_mantissaBitsWithoutImplicit,
        binary64_exponentBits, binary64_mantissaBits, Nat.cast_ofNat, hlog]
      split_ifs <;> try omega
      have hexp : (((unpackExponent (spec := .binary64) b).toNat : ℤ) - (1023 + 52) + 1023 + 52).toNat
          = (unpackExponent (spec := .binary64) b).toNat := by omega
      rw [sign_toBitVec_ofBitVec, hexp, ofNat_toNat_self]
      have hmant : BitVec.ofNat 52 (1#1 ++ unpackMantissa (spec := .binary64) b).toNat =
          unpackMantissa (spec := .binary64) b := by
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_ofNat, toNat_one_append]; omega
      rw [hmant]; exact hb

/-- `pack ∘ unpack` is the identity on `Float.Model`. -/
theorem pack_unpack (f : Float.Model) : Float.Model.pack f.unpack = f := by
  obtain ⟨bits, valid⟩ := f
  simp only [Float.Model.pack, Float.Model.unpack, Float.Model.mk.injEq]
  rw [pack_unpack_bits _ valid]

end FloatRoundtrip
