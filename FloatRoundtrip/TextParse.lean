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

theorem splitAtFirst?_none_of {s : Slice} {p : Char → Bool} {L : List Char}
    (h : s.copy.toList = L) (hL : ∀ x ∈ L, p x = false) : splitAtFirst? s p = none :=
  splitAtFirst?_none (h ▸ hL)

/-! ## Whole numbers -/

/-- The characters of the sign. -/
def signChars (neg : Bool) : List Char := if neg then ['-'] else []

theorem head?_ne_of_dig {A X : List Char} {c : Char} (hA : ∀ x ∈ A, IsDig x) (hAne : A ≠ [])
    (hc : ∀ x, IsDig x → x ≠ c) : (A ++ X).head? ≠ some c := by
  obtain ⟨a, A', rfl⟩ := List.exists_cons_of_ne_nil hAne
  simpa using hc a (hA a (by simp))

theorem sign_cases {s : Slice} {neg : Bool} {rest : List Char}
    (h : s.copy.toList = signChars neg ++ rest) (hr : rest.head? ≠ some '-') :
    (neg = true ∧ ∃ t, s.dropPrefix? '-' = some t ∧ t.copy.toList = rest) ∨
    (neg = false ∧ s.dropPrefix? '-' = none ∧ s.copy.toList = rest) := by
  cases neg
  · simp only [signChars, Bool.false_eq_true, if_false, List.nil_append] at h
    exact .inr ⟨rfl, dropPrefix?_none (h ▸ hr), h⟩
  · simp only [signChars, if_true, List.singleton_append] at h
    exact .inl ⟨rfl, dropPrefix?_some h⟩

theorem not_e_of_dig {L : List Char} (hL : ∀ x ∈ L, IsDig x ∨ x = '.') :
    ∀ x ∈ L, (decide (x = 'e') || decide (x = 'E')) = false := by
  intro x hx
  rcases hL x hx with h | rfl
  · simp [h.ne_e, h.ne_E]
  · decide

theorem not_dot_of_dig {L : List Char} (hL : ∀ x ∈ L, IsDig x) :
    ∀ x ∈ L, decide (x = '.') = false := by
  intro x hx
  simp [(hL x hx).ne_dot]

/-- `decimalParts?` on positional notation `[-]A.B`. -/
theorem decimalParts?_positional {s : Slice} {neg : Bool} {A B : List Char}
    (h : s.copy.toList = signChars neg ++ (A ++ '.' :: B))
    (hA : ∀ c ∈ A, IsDig c) (hB : ∀ c ∈ B, IsDig c) (hAne : A ≠ []) :
    decimalParts? s = some (neg, digitsVal (A ++ B), -(B.length : ℤ)) := by
  have hr := head?_ne_of_dig (X := '.' :: B) hA hAne fun x hx => hx.ne_minus
  unfold decimalParts?
  rcases sign_cases h hr with ⟨rfl, t, hd, ht⟩ | ⟨rfl, hd, ht⟩ <;> rw [hd] <;> dsimp only
  all_goals
    rw [splitAtFirst?_none_of (p := fun c => c = 'e' || c = 'E') ht (not_e_of_dig (by
      intro x hx
      simp only [List.mem_append, List.mem_cons] at hx
      rcases hx with hx | rfl | hx
      · exact .inl (hA x hx)
      · exact .inr rfl
      · exact .inl (hB x hx)))]
    dsimp only
    obtain ⟨l, r, hsp, hl, hr⟩ :=
      splitAtFirst?_some (p := (· = '.')) ht (by simp) (not_dot_of_dig hA)
    have : 0 < A.length := List.length_pos_of_ne_nil hAne
    simp [hsp, digitRun?_of_digits hl hA, digitRun?_of_digits hr hB, digitsVal_append, this]

/-- `decimalParts?` on scientific notation `[-]A[.B]e±K`. -/
theorem decimalParts?_scientific {s : Slice} {neg expNeg dot : Bool} {A B K : List Char}
    (h : s.copy.toList = signChars neg ++
      (A ++ ((if dot then '.' :: B else []) ++ 'e' :: (if expNeg then '-' else '+') :: K)))
    (hA : ∀ c ∈ A, IsDig c) (hB : ∀ c ∈ B, IsDig c) (hK : ∀ c ∈ K, IsDig c)
    (hAne : A ≠ []) (hKne : K ≠ []) (hdot : dot = false → B = []) :
    decimalParts? s = some (neg, digitsVal (A ++ B),
      (if expNeg then -(digitsVal K : ℤ) else digitsVal K) - B.length) := by
  have hr := head?_ne_of_dig (X := (if dot then '.' :: B else []) ++
    'e' :: (if expNeg then '-' else '+') :: K) hA hAne fun x hx => hx.ne_minus
  have hF : ∀ x ∈ A ++ (if dot then '.' :: B else []), IsDig x ∨ x = '.' := by
    intro x hx
    simp only [List.mem_append] at hx
    rcases hx with hx | hx
    · exact .inl (hA x hx)
    · cases dot
      · simp at hx
      · simp only [if_true, List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact .inr rfl
        · exact .inl (hB x hx)
  unfold decimalParts?
  rcases sign_cases h hr with ⟨rfl, t, hd, ht⟩ | ⟨rfl, hd, ht⟩ <;> rw [hd] <;> dsimp only
  all_goals
    rw [← List.append_assoc] at ht
    obtain ⟨l, r, hsp, hl, hr⟩ :=
      splitAtFirst?_some (p := fun c => c = 'e' || c = 'E') ht (by simp) (not_e_of_dig hF)
    rw [hsp]
    dsimp only
    have hlen : 0 < A.length := List.length_pos_of_ne_nil hAne
    have hfrac : ∃ ip fp : Slice, ip.copy.toList = A ∧ fp.copy.toList = B ∧
        ((splitAtFirst? l fun x => decide (x = '.')) = some (ip, fp) ∨
          ((splitAtFirst? l fun x => decide (x = '.')) = none ∧ ip = l ∧
            fp = l.sliceFrom l.endPos)) := by
      cases dot
      · rw [hdot rfl]
        simp only [Bool.false_eq_true, if_false, List.append_nil] at hl
        refine ⟨l, l.sliceFrom l.endPos, hl, ?_,
          .inr ⟨splitAtFirst?_none_of hl (not_dot_of_dig hA), rfl, rfl⟩⟩
        rw [Slice.copy_sliceFrom_endPos, String.toList_empty]
      · simp only [if_true] at hl
        obtain ⟨ip, fp, hsp', hip, hfp⟩ :=
          splitAtFirst?_some (p := (· = '.')) hl (by simp) (not_dot_of_dig hA)
        exact ⟨ip, fp, hip, hfp, .inl hsp'⟩
    obtain ⟨ip, fp, hip, hfp, hsplit⟩ := hfrac
    have hdig := digitRun?_of_digits hip hA
    have hdig' := digitRun?_of_digits hfp hB
    rcases hsplit with hsplit | ⟨hsplit, rfl, rfl⟩
    all_goals
      cases expNeg
      · simp only [Bool.false_eq_true, if_false] at hr
        obtain ⟨rest, hrest, hk⟩ := dropPrefix?_some hr
        rw [dropPrefix?_none (c := '-') (by simp [hr]), hrest]
        simp [toNat?_of_digits hk hKne hK, hsplit, hdig, hdig', digitsVal_append, hlen]
      · simp only [if_true] at hr
        obtain ⟨rest, hrest, hk⟩ := dropPrefix?_some hr
        rw [hrest]
        simp [toNat?_of_digits hk hKne hK, hsplit, hdig, hdig', digitsVal_append, hlen]

end FloatRoundtrip
