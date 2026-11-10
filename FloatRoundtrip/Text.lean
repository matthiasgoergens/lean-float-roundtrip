import FloatRoundtrip.FastPath
import FloatRoundtrip.TextParse

/-!
# The round trip through text

`toFloat?` reads every string that `layoutDecimal` writes back as the same digits and exponent,
up to trailing zeros, and so reads `modelToString x.toModel` back as `x` for every finite `x`.
-/

open String Float.Model Float.Model.UnpackedFloat

namespace FloatRoundtrip

/-! ## Writing digits -/

theorem toList_pushAll (s : String) (cs : List Char) :
    (pushAll s cs).toList = s.toList ++ cs := by
  induction cs generalizing s with
  | nil => simp [pushAll]
  | cons c cs ih => simp [pushAll, ih, String.toList_push]

theorem toList_pushZeros (s : String) (k : ℕ) :
    (pushZeros s k).toList = s.toList ++ List.replicate k '0' := by
  induction k generalizing s with
  | zero => simp [pushZeros]
  | succ k ih => simp [pushZeros, ih, String.toList_push, List.replicate_succ]

theorem decimalDigits_succ (fuel n : ℕ) (acc : List Char) :
    decimalDigits (fuel + 1) n acc = if n < 10 then Char.ofNat ('0'.toNat + n % 10) :: acc
      else decimalDigits fuel (n / 10) (Char.ofNat ('0'.toNat + n % 10) :: acc) := rfl

theorem decimalDigits_acc : ∀ (fuel n : ℕ) (acc : List Char),
    decimalDigits fuel n acc = decimalDigits fuel n [] ++ acc
  | 0, _, _ => rfl
  | fuel + 1, n, acc => by
    by_cases h : n < 10
    · simp [decimalDigits_succ, h]
    · simp only [decimalDigits_succ, h, if_false]
      rw [decimalDigits_acc fuel (n / 10) (Char.ofNat ('0'.toNat + n % 10) :: acc),
        decimalDigits_acc fuel (n / 10) [Char.ofNat ('0'.toNat + n % 10)]]
      simp

theorem digitsVal_single {d : ℕ} (hd : d < 10) :
    digitsVal [Char.ofNat ('0'.toNat + d)] = d := by
  show 0 * 10 + ((Char.ofNat ('0'.toNat + d)).toNat - '0'.toNat) = d
  rw [(isDig_facts d hd).2.2.2.2.2.2.2, zero_mul, zero_add]

theorem digitsVal_zero_single : digitsVal ['0'] = 0 := by decide

theorem decimalDigits_spec (fuel : ℕ) : ∀ n, n < 10 ^ (fuel + 1) →
    (∀ c ∈ decimalDigits (fuel + 1) n [], IsDig c) ∧
      digitsVal (decimalDigits (fuel + 1) n []) = n ∧ decimalDigits (fuel + 1) n [] ≠ [] := by
  induction fuel with
  | zero =>
    intro n hn
    have h : n < 10 := by simpa using hn
    simp only [decimalDigits_succ, h, if_true, Nat.mod_eq_of_lt h]
    refine ⟨?_, digitsVal_single h, by simp⟩
    simp only [List.mem_singleton]
    rintro c rfl
    exact ⟨n, h, rfl⟩
  | succ fuel ih =>
    intro n hn
    have hmod : n % 10 < 10 := Nat.mod_lt _ (by norm_num)
    by_cases h : n < 10
    · simp only [decimalDigits_succ, h, if_true, Nat.mod_eq_of_lt h]
      refine ⟨?_, digitsVal_single h, by simp⟩
      simp only [List.mem_singleton]
      rintro c rfl
      exact ⟨n, h, rfl⟩
    · obtain ⟨h1, h2, -⟩ := ih (n / 10) (by
        rw [Nat.div_lt_iff_lt_mul (by norm_num)]
        simpa [pow_succ] using hn)
      rw [decimalDigits_succ, if_neg h, decimalDigits_acc]
      refine ⟨?_, ?_, by simp⟩
      · intro c hc
        simp only [List.mem_append, List.mem_singleton] at hc
        rcases hc with hc | rfl
        · exact h1 c hc
        · exact ⟨_, hmod, rfl⟩
      · rw [digitsVal_append, h2, digitsVal_single hmod]
        simp only [List.length_singleton, pow_one]
        omega

theorem lt_ten_pow_log2 (n : ℕ) : n < 10 ^ (Nat.log2 n + 1 + 1) :=
  calc n < 2 ^ (Nat.log2 n + 1) := Nat.lt_log2_self
    _ ≤ 10 ^ (Nat.log2 n + 1) := Nat.pow_le_pow_left (by norm_num) _
    _ ≤ 10 ^ (Nat.log2 n + 1 + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)

/-- The digits `decimalDigits` writes for `n` are digits, read back as `n`, and never empty. -/
theorem digits_facts (n : ℕ) :
    (∀ c ∈ decimalDigits (Nat.log2 n + 2) n [], IsDig c) ∧
      digitsVal (decimalDigits (Nat.log2 n + 2) n []) = n ∧
      decimalDigits (Nat.log2 n + 2) n [] ≠ [] :=
  decimalDigits_spec (Nat.log2 n + 1) n (lt_ten_pow_log2 n)

theorem exists_dig {L A R : List Char} {neg : Bool} (h : L = signChars neg ++ (A ++ R))
    (hA : ∀ c ∈ A, IsDig c) (hAne : A ≠ []) : ∃ d ∈ L, IsDig d := by
  obtain ⟨a, A', rfl⟩ := List.exists_cons_of_ne_nil hAne
  exact ⟨a, by simp [h], hA a (by simp)⟩

theorem mem_take_dig {ds : List Char} (hd : ∀ c ∈ ds, IsDig c) (k : ℕ) :
    ∀ c ∈ ds.take k, IsDig c := fun c hc => hd c (List.mem_of_mem_take hc)

theorem mem_drop_dig {ds : List Char} (hd : ∀ c ∈ ds, IsDig c) (k : ℕ) :
    ∀ c ∈ ds.drop k, IsDig c := fun c hc => hd c (List.mem_of_mem_drop hc)

/-! ## The four layouts -/

theorem parts_positional {s : Slice} {neg : Bool} {A B : List Char}
    (h : s.copy.toList = signChars neg ++ (A ++ '.' :: B))
    (hA : ∀ c ∈ A, IsDig c) (hB : ∀ c ∈ B, IsDig c) (hAne : A ≠ []) :
    decimalParts? s = some (neg, digitsVal (A ++ B), -(B.length : ℤ)) ∧
      ∃ d ∈ s.copy.toList, IsDig d :=
  ⟨decimalParts?_positional h hA hB hAne, exists_dig h hA hAne⟩

theorem parts_scientific {s : Slice} {neg expNeg dot : Bool} {A B K : List Char}
    (h : s.copy.toList = signChars neg ++
      (A ++ ((if dot then '.' :: B else []) ++ 'e' :: (if expNeg then '-' else '+') :: K)))
    (hA : ∀ c ∈ A, IsDig c) (hB : ∀ c ∈ B, IsDig c) (hK : ∀ c ∈ K, IsDig c)
    (hAne : A ≠ []) (hKne : K ≠ []) (hdot : dot = false → B = []) :
    decimalParts? s = some (neg, digitsVal (A ++ B),
      (if expNeg then -(digitsVal K : ℤ) else digitsVal K) - B.length) ∧
      ∃ d ∈ s.copy.toList, IsDig d :=
  ⟨decimalParts?_scientific h hA hB hK hAne hKne hdot, exists_dig h hA hAne⟩

/--
Whatever layout `layoutDecimal` picks, `decimalParts?` reads back the sign and digits `M` and an
exponent `E` with `M * 10 ^ E = c * 10 ^ q`.
-/
theorem layout_parts {sgn : String} {neg : Bool} (hs : sgn.toList = signChars neg) (c : ℕ)
    (q : ℤ) : ∃ M E, (decimalParts? (layoutDecimal sgn c q).toSlice = some (neg, M, E) ∧
      ∃ d ∈ (layoutDecimal sgn c q).toSlice.copy.toList, IsDig d) ∧
      (M : ℚ) * 10 ^ E = c * 10 ^ q := by
  obtain ⟨hdig, hval, hne⟩ := digits_facts c
  have hn : 0 < (decimalDigits (Nat.log2 c + 2) c []).length := List.length_pos_of_ne_nil hne
  unfold layoutDecimal
  generalize decimalDigits (Nat.log2 c + 2) c [] = ds at hdig hval hne hn ⊢
  dsimp only
  have hM : ∀ {A B : List Char}, A ++ B = ds → digitsVal (A ++ B) = c := fun h => h ▸ hval
  by_cases h1 : (ds.length : ℤ) + q ≤ -4 ∨ (ds.length : ℤ) + q > 16
  · -- scientific notation
    rw [if_pos h1]
    generalize hexp : (ds.length : ℤ) + q - 1 = exp
    obtain ⟨hedig, heval, hene⟩ := digits_facts exp.natAbs
    have hKv : digitsVal ((if exp.natAbs < 10 then ['0'] else []) ++
        decimalDigits (Nat.log2 exp.natAbs + 2) exp.natAbs []) = exp.natAbs := by
      split_ifs
      · rw [digitsVal_append, heval, digitsVal_zero_single, zero_mul, zero_add]
      · rw [List.nil_append, heval]
    refine ⟨_, _, parts_scientific (dot := decide (ds.length > 1))
      (expNeg := decide (exp < 0)) (A := List.take 1 ds) (B := List.drop 1 ds)
      (K := (if exp.natAbs < 10 then ['0'] else []) ++
        decimalDigits (Nat.log2 exp.natAbs + 2) exp.natAbs []) ?hl (mem_take_dig hdig 1) (mem_drop_dig hdig 1) ?hK ?hAne
      ?hKne ?hdot, ?val⟩
    case hl =>
      rw [String.copy_toSlice]
      simp only [decide_eq_true_eq]
      split_ifs <;> simp [toList_pushAll, String.toList_push, hs]
    case hK =>
      intro x hx
      simp only [List.mem_append] at hx
      rcases hx with hx | hx
      · split_ifs at hx
        · simp only [List.mem_singleton] at hx; exact hx ▸ isDig_zero
        · simp at hx
      · exact hedig x hx
    case hAne => simpa using hne
    case hKne => simp [hene]
    case hdot =>
      intro h
      apply List.drop_eq_nil_of_le
      simp only [decide_eq_false_iff_not, not_lt] at h
      exact h
    case val =>
      have hE : (if decide (exp < 0) = true then
          -(digitsVal ((if exp.natAbs < 10 then ['0'] else []) ++
            decimalDigits (Nat.log2 exp.natAbs + 2) exp.natAbs []) : ℤ)
          else (digitsVal ((if exp.natAbs < 10 then ['0'] else []) ++
            decimalDigits (Nat.log2 exp.natAbs + 2) exp.natAbs []) : ℤ)) -
          ((List.drop 1 ds).length : ℤ) = q := by
        rw [hKv, List.length_drop]
        by_cases hneg : exp < 0
        · simp only [hneg, decide_true, if_true]
          rw [Int.natCast_natAbs, abs_of_neg hneg]
          omega
        · simp only [hneg, decide_false, Bool.false_eq_true, if_false]
          rw [Int.natCast_natAbs, abs_of_nonneg (not_lt.1 hneg)]
          omega
      rw [hE, hM (List.take_append_drop 1 ds)]
  · rw [if_neg h1]
    by_cases h2 : (ds.length : ℤ) + q ≤ 0
    · -- `0.000ddd`
      rw [if_pos h2]
      refine ⟨_, _, parts_positional (A := ['0'])
        (B := List.replicate ((-((ds.length : ℤ) + q)).toNat) '0' ++ ds) ?hl (by simp [isDig_zero])
        ?hB (by simp), ?val⟩
      case hl =>
        rw [String.copy_toSlice]
        simp [toList_pushAll, toList_pushZeros, String.toList_push, hs]
      case hB =>
        intro x hx
        simp only [List.mem_append, List.mem_replicate] at hx
        rcases hx with ⟨-, rfl⟩ | hx
        · exact isDig_zero
        · exact hdig x hx
      case val =>
        have hv : digitsVal (['0'] ++
            (List.replicate ((-((ds.length : ℤ) + q)).toNat) '0' ++ ds)) = c := by
          rw [digitsVal_append, digitsVal_append, digitsVal_replicate_zero, hval,
            digitsVal_zero_single]
          simp
        have hE : -(((List.replicate ((-((ds.length : ℤ) + q)).toNat) '0' ++ ds).length : ℕ) :
            ℤ) = q := by
          simp only [List.length_append, List.length_replicate]
          omega
        rw [hv, hE]
    · rw [if_neg h2]
      by_cases h3 : ds.length ≤ ((ds.length : ℤ) + q).toNat
      · -- `ddd000.0`
        rw [if_pos h3]
        refine ⟨_, _, parts_positional
          (A := ds ++ List.replicate (((ds.length : ℤ) + q).toNat - ds.length) '0')
          (B := ['0']) ?hl ?hA (by simp [isDig_zero]) ?hAne, ?val⟩
        case hl =>
          rw [String.copy_toSlice]
          simp [toList_pushAll, toList_pushZeros, String.toList_push, hs]
        case hA =>
          intro x hx
          simp only [List.mem_append, List.mem_replicate] at hx
          rcases hx with hx | ⟨-, rfl⟩
          · exact hdig x hx
          · exact isDig_zero
        case hAne => simp [hne]
        case val =>
          generalize hk : ((ds.length : ℤ) + q).toNat - ds.length = k
          have hq : q = k := by omega
          have hv : digitsVal ((ds ++ List.replicate k '0') ++ ['0']) = c * 10 ^ k * 10 := by
            rw [digitsVal_append, digitsVal_append, digitsVal_replicate_zero, hval,
              digitsVal_zero_single]
            simp
          rw [hv, hq]
          push_cast
          rw [zpow_natCast, List.length_singleton, Nat.cast_one, zpow_neg_one]
          field_simp
      · -- `dd.ddd`
        rw [if_neg h3]
        refine ⟨_, _, parts_positional (A := ds.take ((ds.length : ℤ) + q).toNat)
          (B := ds.drop ((ds.length : ℤ) + q).toNat) ?hl (mem_take_dig hdig _)
          (mem_drop_dig hdig _) ?hAne, ?val⟩
        case hl =>
          rw [String.copy_toSlice]
          simp [toList_pushAll, String.toList_push, hs]
        case hAne =>
          simp only [ne_eq, List.take_eq_nil_iff, hne, or_false]
          omega
        case val =>
          have hE : -((ds.drop ((ds.length : ℤ) + q).toNat).length : ℤ) = q := by
            rw [List.length_drop]
            omega
          rw [hE, hM (List.take_append_drop _ ds)]

/-! ## Reading back -/

theorem no_dig_of {l : List Char} (h : ∀ c ∈ l, c.isDigit = false) : ∀ d ∈ l, ¬ IsDig d := by
  intro d hd hdig
  have h1 := h d hd
  rw [hdig.isDigit] at h1
  exact Bool.noConfusion h1

theorem inf_no_dig : ∀ d ∈ "inf".toList, ¬ IsDig d := by
  refine no_dig_of ?_
  rw [show "inf".toList = ['i', 'n', 'f'] by decide +kernel]
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> rfl

theorem neg_inf_no_dig : ∀ d ∈ "-inf".toList, ¬ IsDig d := by
  refine no_dig_of ?_
  rw [show "-inf".toList = ['-', 'i', 'n', 'f'] by decide +kernel]
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> rfl

theorem nan_no_dig : ∀ d ∈ "NaN".toList, ¬ IsDig d := by
  refine no_dig_of ?_
  rw [show "NaN".toList = ['N', 'a', 'N'] by decide +kernel]
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> rfl

theorem toFloat?_of_parts {s : Slice} {neg : Bool} {M : ℕ} {E : ℤ}
    (hd : ∃ d ∈ s.copy.toList, IsDig d) (hp : decimalParts? s = some (neg, M, E)) :
    toFloat? s = some (if neg then -Float.ofScientific M (decide (E < 0)) E.natAbs
      else Float.ofScientific M (decide (E < 0)) E.natAbs) := by
  have hne : ∀ w : String, (∀ d ∈ w.toList, ¬ IsDig d) → (s == w.toSlice) = false := by
    intro w hw
    rw [Slice.beq_eq_false_iff, String.copy_toSlice]
    intro heq
    obtain ⟨d, hd, hdig⟩ := hd
    rw [heq] at hd
    exact hw d hd hdig
  unfold toFloat?
  simp only [hne "inf" inf_no_dig, hne "-inf" neg_inf_no_dig, hne "NaN" nan_no_dig,
    Bool.false_eq_true, ↓reduceIte, hp, Option.map_some]
  cases neg <;> rfl

/--
**The round trip through text.**  For every finite float `x`, zeros included, `toFloat?` reads
the string that the printer writes for `x` back as `x`.
-/
theorem toFloat?_modelToString (x : Float) (hx : x.isFinite = true) :
    toFloat? (modelToString x.toModel).toSlice = some x := by
  have hfin : x.toModel.unpack.isFinite = true := hx
  unfold modelToString
  cases hu : x.toModel.unpack with
  | infinity s => rw [hu] at hfin; simp [UnpackedFloat.isFinite] at hfin
  | notANumber => rw [hu] at hfin; simp [UnpackedFloat.isFinite] at hfin
  | zero s =>
    have hxm : x.toModel = Float.Model.pack (.zero s) := by rw [← pack_unpack x.toModel, hu]
    cases s with
    | positive =>
      have hp := decimalParts?_positional (s := "0.0".toSlice) (neg := false) (A := ['0'])
        (B := ['0']) (by rw [String.copy_toSlice]; decide +kernel) (by simp [isDig_zero])
        (by simp [isDig_zero]) (by simp)
      rw [show toDecimalString .binary64 (.zero .positive) = "0.0" from rfl,
        toFloat?_of_parts ⟨'0', by rw [String.copy_toSlice]; decide +kernel, isDig_zero⟩ hp]
      congr 1
      apply float_ext
      rw [hxm]
      decide +kernel
    | negative =>
      have hp := decimalParts?_positional (s := "-0.0".toSlice) (neg := true) (A := ['0'])
        (B := ['0']) (by rw [String.copy_toSlice]; decide +kernel) (by simp [isDig_zero])
        (by simp [isDig_zero]) (by simp)
      rw [show toDecimalString .binary64 (.zero .negative) = "-0.0" from rfl,
        toFloat?_of_parts ⟨'0', by rw [String.copy_toSlice]; decide +kernel, isDig_zero⟩ hp]
      congr 1
      apply float_ext
      rw [hxm]
      decide +kernel
  | finite s m e h =>
    obtain ⟨hc, he⟩ := unpack_finite hu
    obtain ⟨M, E, ⟨hp, hdig⟩, hval⟩ := layout_parts (sgn := if s = .negative then "-" else "")
      (neg := decide (s = .negative)) (by cases s <;> decide) (printedDigits m e).1
      (printedDigits m e).2
    have hdef : toDecimalString .binary64 (.finite s m e h) =
        layoutDecimal (if s = .negative then "-" else "") (printedDigits m e).1
          (printedDigits m e).2 := rfl
    rw [hdef, toFloat?_of_parts hdig hp]
    congr 1
    have hnear : Near .binary64 m e (M * 10 ^ E) := by
      rw [hval]
      exact printedDigits_near hc he
    have hfast := floatOfScientific_of_near hc he hnear
    apply float_ext
    cases s with
    | positive =>
      simp only [reduceCtorEq, decide_false, Bool.false_eq_true, ↓reduceIte]
      rw [hfast, ← pack_unpack x.toModel, hu]
    | negative =>
      simp only [decide_true, ↓reduceIte]
      show Float.Model.pack (Float.ofScientific _ _ _).toModel.unpack.neg = _
      rw [hfast, model_unpack_pack hc he, ← pack_unpack x.toModel, hu]
      rfl

end FloatRoundtrip
