import FloatRoundtrip.ToFloat
import Mathlib.Tactic

/-!
# What the parser makes of a well-formed decimal

`decimalParts?` splits `[-]A.B` and `[-]A[.B]e±K`, for runs of decimal digits `A`, `B` and `K`, into
the sign, the digits `A ++ B` and the exponent.  Everything is stated about the characters of a
slice, `s.copy.toList`.
-/

open String

namespace FloatRoundtrip

/-! ## Digit characters -/

/-- `c` is the character of a decimal digit, as `decimalDigits` writes it. -/
def IsDig (c : Char) : Prop := ∃ d, d < 10 ∧ c = Char.ofNat ('0'.toNat + d)

instance : DecidablePred IsDig := fun _ => by unfold IsDig; infer_instance

theorem isDig_facts : ∀ d, d < 10 → (Char.ofNat ('0'.toNat + d)).isDigit = true ∧
    Char.ofNat ('0'.toNat + d) ≠ '_' ∧ Char.ofNat ('0'.toNat + d) ≠ 'e' ∧
    Char.ofNat ('0'.toNat + d) ≠ 'E' ∧ Char.ofNat ('0'.toNat + d) ≠ '.' ∧
    Char.ofNat ('0'.toNat + d) ≠ '-' ∧ Char.ofNat ('0'.toNat + d) ≠ '+' ∧
    (Char.ofNat ('0'.toNat + d)).toNat - '0'.toNat = d := by
  decide

theorem IsDig.isDigit {c : Char} (h : IsDig c) : c.isDigit = true := by
  obtain ⟨d, hd, rfl⟩ := h; exact (isDig_facts d hd).1
theorem IsDig.ne_underscore {c : Char} (h : IsDig c) : c ≠ '_' := by
  obtain ⟨d, hd, rfl⟩ := h; exact (isDig_facts d hd).2.1
theorem IsDig.ne_e {c : Char} (h : IsDig c) : c ≠ 'e' := by
  obtain ⟨d, hd, rfl⟩ := h; exact (isDig_facts d hd).2.2.1
theorem IsDig.ne_E {c : Char} (h : IsDig c) : c ≠ 'E' := by
  obtain ⟨d, hd, rfl⟩ := h; exact (isDig_facts d hd).2.2.2.1
theorem IsDig.ne_dot {c : Char} (h : IsDig c) : c ≠ '.' := by
  obtain ⟨d, hd, rfl⟩ := h; exact (isDig_facts d hd).2.2.2.2.1
theorem IsDig.ne_minus {c : Char} (h : IsDig c) : c ≠ '-' := by
  obtain ⟨d, hd, rfl⟩ := h; exact (isDig_facts d hd).2.2.2.2.2.1
theorem IsDig.ne_plus {c : Char} (h : IsDig c) : c ≠ '+' := by
  obtain ⟨d, hd, rfl⟩ := h; exact (isDig_facts d hd).2.2.2.2.2.2.1

theorem isDig_zero : IsDig '0' := ⟨0, by decide, by decide⟩

/-- The value of a run of digit characters, most significant first. -/
def digitsVal (ds : List Char) : ℕ := ds.foldl (fun n c => n * 10 + (c.toNat - '0'.toNat)) 0

theorem foldl_digits (ds : List Char) (n : ℕ) :
    ds.foldl (fun n c => n * 10 + (c.toNat - '0'.toNat)) n = n * 10 ^ ds.length + digitsVal ds := by
  induction ds generalizing n with
  | nil => simp [digitsVal]
  | cons c ds ih =>
    simp only [digitsVal, List.foldl_cons, List.length_cons] at ih ⊢
    rw [ih, ih (0 * 10 + _)]
    ring

theorem digitsVal_append (a b : List Char) :
    digitsVal (a ++ b) = digitsVal a * 10 ^ b.length + digitsVal b := by
  unfold digitsVal
  rw [List.foldl_append, foldl_digits]
  rfl

theorem digitsVal_replicate_zero (k : ℕ) : digitsVal (List.replicate k '0') = 0 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ', digitsVal_append, ih]
    decide

/-! ## Slices -/

theorem toList_eq_nil_iff {s : Slice} : s.copy.toList = [] ↔ s.isEmpty = true := by
  rw [← Slice.copy_eq_empty_iff, ← String.toList_inj, String.toList_empty]

theorem forIn_digits {β : Type} {ds : List Char} (hd : ∀ c ∈ ds, IsDig c) (init y : β)
    (f : Char → β → Id (ForInStep β)) (hf : ∀ c, IsDig c → ∀ st, f c st = pure (.yield y)) :
    forIn ds init f = pure (if ds = [] then init else y) := by
  induction ds generalizing init with
  | nil => simp
  | cons c ds ih =>
    rw [List.forIn_cons, hf c (hd c (by simp)) init]
    simp only [pure_bind]
    rw [ih (fun c h => hd c (by simp [h]))]
    split <;> simp

theorem isNat_of_digits {s : Slice} {ds : List Char} (h : s.copy.toList = ds) (hne : ds ≠ [])
    (hd : ∀ c ∈ ds, IsDig c) : s.isNat = true := by
  unfold Slice.isNat
  simp only [Id.run, Slice.forIn_eq_forIn_toList, h]
  rw [forIn_digits hd _ ((none : Option Bool), true)]
  · simp [hne]; rfl
  · intro c hc st
    simp [hc.ne_underscore, hc.isDigit]

theorem foldl_underscore {ds : List Char} (hd : ∀ c ∈ ds, IsDig c) (n : ℕ) :
    ds.foldl (fun n c => if c = '_' then n else n * 10 + (c.toNat - '0'.toNat)) n =
      ds.foldl (fun n c => n * 10 + (c.toNat - '0'.toNat)) n := by
  induction ds generalizing n with
  | nil => rfl
  | cons c ds ih =>
    simp only [List.foldl_cons, if_neg (hd c (by simp)).ne_underscore]
    exact ih (fun c h => hd c (by simp [h])) _

theorem foldl_count {ds : List Char} (hd : ∀ c ∈ ds, IsDig c) (k : ℕ) :
    ds.foldl (fun k c => if c = '_' then k else k + 1) k = k + ds.length := by
  induction ds generalizing k with
  | nil => rfl
  | cons c ds ih =>
    simp only [List.foldl_cons, if_neg (hd c (by simp)).ne_underscore, List.length_cons]
    rw [ih (fun c h => hd c (by simp [h]))]
    omega

theorem digitRun?_of_digits {s : Slice} {ds : List Char} (h : s.copy.toList = ds)
    (hd : ∀ c ∈ ds, IsDig c) : digitRun? s = some (digitsVal ds, ds.length) := by
  unfold digitRun?
  by_cases hne : ds = []
  · subst hne
    rw [if_pos (toList_eq_nil_iff.1 h)]
    rfl
  · have he : ¬ s.isEmpty = true := fun h' => hne (h ▸ toList_eq_nil_iff.2 h')
    rw [if_neg he, if_pos (isNat_of_digits h hne hd)]
    simp only [Slice.foldl_eq_foldl_toList, h, foldl_underscore hd, foldl_count hd, zero_add]
    rfl

theorem toNat?_of_digits {s : Slice} {ds : List Char} (h : s.copy.toList = ds) (hne : ds ≠ [])
    (hd : ∀ c ∈ ds, IsDig c) : s.toNat? = some (digitsVal ds) := by
  unfold Slice.toNat?
  rw [if_pos (isNat_of_digits h hne hd)]
  simp only [Slice.foldl_eq_foldl_toList, h, foldl_underscore hd]
  rfl

theorem dropPrefix?_some {s : Slice} {c : Char} {r : List Char} (h : s.copy.toList = c :: r) :
    ∃ res, s.dropPrefix? c = some res ∧ res.copy.toList = r := by
  cases hres : s.dropPrefix? c with
  | none =>
    rw [Slice.dropPrefix?_eq_none_iff, Slice.startsWith_char_eq_head?, h] at hres
    simp at hres
  | some res =>
    refine ⟨res, rfl, ?_⟩
    have := congrArg String.toList (Slice.eq_append_of_dropPrefix?_char_eq_some hres)
    rw [h, String.toList_append, String.toList_singleton] at this
    simp only [List.singleton_append, List.cons.injEq] at this
    exact this.2.symm

theorem dropPrefix?_none {s : Slice} {c : Char} (h : s.copy.toList.head? ≠ some c) :
    s.dropPrefix? c = none := by
  rw [Slice.dropPrefix?_eq_none_iff, Slice.startsWith_char_eq_head?]
  simpa using h

theorem first_split_unique {p : Char → Bool} {c₁ c₂ : Char} {b₁ b₂ : List Char}
    (h₁ : p c₁ = true) (h₂ : p c₂ = true) :
    ∀ {a₁ a₂ : List Char}, a₁ ++ c₁ :: b₁ = a₂ ++ c₂ :: b₂ →
      (∀ x ∈ a₁, p x = false) → (∀ x ∈ a₂, p x = false) → a₁ = a₂ ∧ b₁ = b₂
  | [], [], h, _, _ => by simp_all
  | [], x :: a₂, h, _, ha₂ => by
    simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
    obtain ⟨rfl, -⟩ := h
    simp_all
  | x :: a₁, [], h, ha₁, _ => by
    simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
    obtain ⟨rfl, -⟩ := h
    simp_all
  | x :: a₁, y :: a₂, h, ha₁, ha₂ => by
    simp only [List.cons_append, List.cons.injEq] at h
    obtain ⟨rfl, h⟩ := h
    obtain ⟨rfl, rfl⟩ := first_split_unique h₁ h₂ h (fun z hz => ha₁ z (by simp [hz]))
      (fun z hz => ha₂ z (by simp [hz]))
    simp

theorem splitAtFirst?_some {s : Slice} {p : Char → Bool} {a b : List Char} {c : Char}
    (h : s.copy.toList = a ++ c :: b) (hc : p c = true) (ha : ∀ x ∈ a, p x = false) :
    ∃ l r, splitAtFirst? s p = some (l, r) ∧ l.copy.toList = a ∧ r.copy.toList = b := by
  unfold splitAtFirst?
  cases hf : s.find? p with
  | none =>
    exfalso
    have h1 := Slice.isSome_find? p (s := s)
    rw [hf, Slice.contains_bool_eq, h] at h1
    have h2 := List.any_eq_false.1 h1.symm c (by simp)
    exact h2 hc
  | some pos =>
    obtain ⟨t, c', u, hs, hc', ht⟩ := Slice.find?_bool_eq_some_iff_splits.1 hf
    have hl := congrArg String.toList hs.eq_append
    rw [h, String.toList_append, String.toList_append, String.toList_singleton,
      List.singleton_append] at hl
    obtain ⟨hta, hub⟩ := first_split_unique hc hc' hl ha ht
    refine ⟨_, _, rfl, ?_, ?_⟩
    · rw [hs.copy_sliceTo_eq]; exact hta.symm
    · rw [Slice.toList_copy_drop, hs.copy_sliceFrom_eq, String.toList_append,
        String.toList_singleton]
      simpa using hub.symm

theorem splitAtFirst?_none {s : Slice} {p : Char → Bool}
    (h : ∀ x ∈ s.copy.toList, p x = false) : splitAtFirst? s p = none := by
  unfold splitAtFirst?
  have h1 := Slice.isSome_find? p (s := s)
  rw [Slice.contains_bool_eq] at h1
  have h2 : s.find? p = none := by
    rw [← Option.not_isSome_iff_eq_none, h1]
    simpa using h
  rw [h2]
  rfl

end FloatRoundtrip
