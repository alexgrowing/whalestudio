import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockJointMultiplicity.GlobalTheory
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockJointMultiplicity.MemLeftHighestWeightOfIsMinimalJointVector
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockJointMultiplicity.LoweringPartRightActionInlInr
import Lemmata.B1959r.Imports

noncomputable section

open Matrix FockH1Action MvPolynomial

namespace PI.FJMS

open PI.FJM PI.FJMP

theorem pos_iff_lt_nP {n : ℕ} (f : Fin n → ℚ) (hseg : ∀ i i' : Fin n, i < i' → 0 < f i' → 0 < f i)
    (i : Fin n) : 0 < f i ↔ i.val < nP f := by
  first | exact Bl.general_b_fact_upper_bis_form.goal1 .. | (apply Bl.general_b_fact_upper_bis_form.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_upper_bis_form.goal1 <;> assumption) | (apply @Bl.general_b_fact_upper_bis_form.goal1 <;> assumption) | (intros; apply @Bl.general_b_fact_upper_bis_form.goal1 <;> assumption) | (apply @Bl.general_b_fact_upper_bis_form.goal1 <;> first | assumption | infer_instance) | exact @Bl.general_b_fact_upper_bis_form.goal1 n f hseg i | exact @Bl.general_b_fact_upper_bis_form.goal1 n f hseg | exact @Bl.general_b_fact_upper_bis_form.goal1 n f | exact @Bl.general_b_fact_upper_bis_form.goal1 n

theorem neg_iff_nN {n : ℕ} (f : Fin n → ℚ) (hseg : ∀ i i' : Fin n, i < i' → f i < 0 → f i' < 0)
    (i : Fin n) : f i < 0 ↔ n ≤ i.val + nN f := by
  constructor
  · intro hi
    have hsub : Finset.Ici i ⊆ Finset.univ.filter (fun x => f x < 0) := by
      intro x hx
      rw [Finset.mem_Ici] at hx
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      rcases hx.lt_or_eq with h | h
      · exact hseg i x h hi
      · rw [← h]; exact hi
    have h2 := Finset.card_le_card hsub
    rw [Fin.card_Ici] at h2
    show n ≤ i.val + (Finset.univ.filter fun x => f x < 0).card
    have := i.isLt
    omega
  · intro hi
    by_contra hn
    have hsub : Finset.univ.filter (fun x => f x < 0) ⊆ Finset.Ioi i := by
      intro x hx
      rw [Finset.mem_filter] at hx
      rw [Finset.mem_Ioi]
      by_contra hle
      push_neg at hle
      rcases hle.lt_or_eq with h | h
      · exact hn (hseg x i h hx.2)
      · rw [← h] at hn; exact hn hx.2
    have h2 := Finset.card_le_card hsub
    rw [Fin.card_Ioi] at h2
    have h3 : n ≤ i.val + (Finset.univ.filter fun x => f x < 0).card := hi
    have := i.isLt
    omega

theorem idxP {n : ℕ} (f : Fin n → ℚ) (hseg : ∀ i i' : Fin n, i < i' → 0 < f i' → 0 < f i)
    (i : Fin n) (h : 0 < f i) : ∃ x : Fin (nP f), Fin.castLE (nP_le_nW f) x = i :=
  ⟨⟨i.val, (pos_iff_lt_nP f hseg i).1 h⟩, Fin.ext rfl⟩

theorem idxN {n : ℕ} (f : Fin n → ℚ) (hseg : ∀ i i' : Fin n, i < i' → f i < 0 → f i' < 0)
    (i : Fin n) (h : f i < 0) : ∃ x : Fin (nN f), Fin.rev (Fin.castLE (nN_le f) x) = i := by
  have h1 := (neg_iff_nN f hseg i).1 h
  have h2 := i.isLt
  refine ⟨⟨n - 1 - i.val, by omega⟩, Fin.ext ?_⟩
  simp only [Fin.val_rev, Fin.val_castLE]
  omega

theorem pos_of_lt {n : ℕ} (f : Fin n → ℚ) (hseg : ∀ i i' : Fin n, i < i' → 0 < f i' → 0 < f i)
    (x : Fin (nP f)) : 0 < f (Fin.castLE (nP_le_nW f) x) :=
  (pos_iff_lt_nP f hseg _).2 (by simp only [Fin.val_castLE]; exact x.isLt)

theorem neg_of_lt {n : ℕ} (f : Fin n → ℚ) (hseg : ∀ i i' : Fin n, i < i' → f i < 0 → f i' < 0)
    (x : Fin (nN f)) : f (Fin.rev (Fin.castLE (nN_le f) x)) < 0 := by
  refine (neg_iff_nN f hseg _).2 ?_
  have := x.isLt
  have := nN_le f
  simp only [Fin.val_rev, Fin.val_castLE]
  omega

section Gen

variable {σ κ : Type*} [Fintype κ]

theorem sum_range_emb {M : Type*} [AddCommMonoid M] {m : ℕ} (j : Fin m → κ) (hj : Function.Injective j)
    (f : κ → M) (hf : ∀ c, c ∉ Set.range j → f c = 0) : ∑ c, f c = ∑ k, f (j k) := by
  classical
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.map ⟨j, hj⟩))
    (fun c _ hc => hf c (fun ⟨k, hk⟩ => hc (Finset.mem_map.2 ⟨k, Finset.mem_univ _, hk⟩))), Finset.sum_map]
  rfl

theorem gR_pos_block {m : ℕ} (u v : κ → σ) (pos : κ → Bool) (j : Fin m → κ) (hj : Function.Injective j)
    (P : MvPolynomial σ ℂ) (hA : ∀ c, c ∉ Set.range j → NoVar P (u c))
    (hB : ∀ c, c ∉ Set.range j → NoVar P (v c)) (hin : ∀ k, pos (j k) = true) :
    gR u v pos P = ∑ k, X (u (j k)) * pderiv (v (j k)) P := by
  unfold gR
  rw [sum_range_emb j hj _ (fun c hc => ?_)]
  · exact Finset.sum_congr rfl (fun k _ => by rw [if_pos (hin k)])
  · split_ifs
    · rw [pderiv_eq_zero_of_noVar (hB c hc), mul_zero]
    · rw [pderiv_eq_zero_of_noVar (hA c hc), mul_zero, neg_zero]

theorem gR_neg_block {m : ℕ} (u v : κ → σ) (pos : κ → Bool) (j : Fin m → κ) (hj : Function.Injective j)
    (P : MvPolynomial σ ℂ) (hA : ∀ c, c ∉ Set.range j → NoVar P (u c))
    (hB : ∀ c, c ∉ Set.range j → NoVar P (v c)) (hin : ∀ k, pos (j k) = false) :
    gR u v pos P = -∑ k, X (v (j k)) * pderiv (u (j k)) P := by
  have h := gR_swap u v pos P
  rw [gR_pos_block v u (fun c => !pos c) j hj P hB hA (fun k => by simp [hin k])] at h
  rw [h, neg_neg]

theorem sw_pos_block {m : ℕ} (e : σ →₀ ℕ) (w : κ → σ) (pos : κ → Bool) (j : Fin m → κ) (hj : Function.Injective j)
    (hA : ∀ c, c ∉ Set.range j → e (w c) = 0) (hin : ∀ k, pos (j k) = true) :
    sw e w pos = ((∑ k, e (w (j k)) : ℕ) : ℤ) := by
  unfold sw
  rw [sum_range_emb j hj _ (fun c hc => by rw [hA c hc]; simp), Nat.cast_sum]
  exact Finset.sum_congr rfl (fun k _ => by rw [if_pos (hin k)])

theorem sw_neg_block {m : ℕ} (e : σ →₀ ℕ) (w : κ → σ) (pos : κ → Bool) (j : Fin m → κ) (hj : Function.Injective j)
    (hA : ∀ c, c ∉ Set.range j → e (w c) = 0) (hin : ∀ k, pos (j k) = false) :
    sw e w pos = -((∑ k, e (w (j k)) : ℕ) : ℤ) := by
  unfold sw
  rw [sum_range_emb j hj _ (fun c hc => by rw [hA c hc]; simp), Nat.cast_sum, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl (fun k _ => by rw [if_neg (by simp [hin k])])

theorem bRow_apply' {m n : ℕ} (ι : Fin m × Fin n → σ) (a b : Fin m) (P : MvPolynomial σ ℂ) :
    bRow ι a b P = ∑ k : Fin n, X (ι (a, k)) * pderiv (ι (b, k)) P := by
  rw [bRow, LinearMap.sum_apply]; simp

theorem bCol_apply' {m n : ℕ} (ι : Fin m × Fin n → σ) (c d : Fin n) (P : MvPolynomial σ ℂ) :
    bCol ι c d P = ∑ i : Fin m, X (ι (i, c)) * pderiv (ι (i, d)) P := by
  rw [bCol, LinearMap.sum_apply]; simp

end Gen

section Block

variable {p q r s : ℕ} {μ : Ix p q → ℚ} {μ' : Ix r s → ℚ} {P : Pol p q r s}

theorem pure_of (hM : MinHyp p q r s μ μ' P) {e : Ln p q r s →₀ ℕ} (he : e ∈ P.support) {l : Ln p q r s}
    (hl : e l ≠ 0) : nu1 p q r s μ l.1 ≠ 0 ∧ nu2 p q r s μ' l.2 ≠ 0 ∧
      (linePos l = true ↔ 0 < nu1 p q r s μ l.1) ∧ (linePos l = true ↔ 0 < nu2 p q r s μ' l.2) :=
  pureJ_of leftDiagonalActionFormula rightDiagonalActionFormula p q r s μ μ' P hM e he l hl

theorem blkHyp_pos (hM : MinHyp p q r s μ μ' P) {m n : ℕ} (iX : Fin m → Ix p q) (jX : Fin n → Ix r s)
    (hi : Function.Injective iX) (hj : Function.Injective jX)
    (hmi : ∀ a b : Fin m, a < b → posC (iX a) (iX b)) (hmj : ∀ c d : Fin n, c < d → posC (jX c) (jX d))
    (hs1 : ∀ (a b : Fin m) (c : Ix r s), linePos ((iX b, c) : Ln p q r s) = linePos ((iX a, c) : Ln p q r s))
    (hs2 : ∀ (c d : Fin n) (a : Ix p q), linePos ((a, jX d) : Ln p q r s) = linePos ((a, jX c) : Ln p q r s))
    (hlp : ∀ i k, linePos ((iX i, jX k) : Ln p q r s) = true)
    (hcol : ∀ (i : Fin m) (c : Ix r s), linePos ((iX i, c) : Ln p q r s) = true → 0 < nu2 p q r s μ' c →
      c ∈ Set.range jX)
    (hrow : ∀ (k : Fin n) (a : Ix p q), linePos ((a, jX k) : Ln p q r s) = true → 0 < nu1 p q r s μ a →
      a ∈ Set.range iX)
    (hnu1 : ∀ i, 0 < nu1 p q r s μ (iX i)) (hnu2 : ∀ k, 0 < nu2 p q r s μ' (jX k))
    (α : Fin m → ℕ) (β : Fin n → ℕ) (hα : ∀ i, α i = ⌊nu1 p q r s μ (iX i)⌋₊)
    (hβ : ∀ k, β k = ⌊nu2 p q r s μ' (jX k)⌋₊) :
    IsBlockHighestWeight (fun x : Fin m × Fin n => ((iX x.1, jX x.2) : Ln p q r s)) α β P := by
  have hw1 := mem_leftHighestWeight_of_isMinimalJointVector hM
  have hw2 := mem_rightHighestWeight_of_isMinimalJointVector hM
  have hP0 : P ≠ 0 := hM.2.1

  have urow : ∀ i c, c ∉ Set.range jX → NoVar P ((iX i, c) : Ln p q r s) := by
    intro i c hc e he
    by_contra hne
    obtain ⟨-, -, h3, h4⟩ := pure_of hM he hne
    exact hc (hcol i c (h3.2 (hnu1 i)) (h4.1 (h3.2 (hnu1 i))))
  have ucol : ∀ k a, a ∉ Set.range iX → NoVar P ((a, jX k) : Ln p q r s) := by
    intro k a ha e he
    by_contra hne
    obtain ⟨-, -, h3, h4⟩ := pure_of hM he hne
    exact ha (hrow k a (h4.2 (hnu2 k)) (h3.1 (h4.2 (hnu2 k))))
  have rowv : ∀ e ∈ P.support, ∀ i, nu1 p q r s μ (iX i) = ((∑ k, e ((iX i, jX k) : Ln p q r s) : ℕ) : ℚ) := by
    intro e he i
    rw [← monomialLeftWeight_eq_weight_sub leftDiagonalActionFormula hw1 e he (iX i)]
    have h := sw_pos_block e (fun c : Ix r s => ((iX i, c) : Ln p q r s)) (fun c => linePos ((iX i, c) : Ln p q r s))
      jX hj (fun c hc => urow i c hc e he) (fun k => hlp i k)
    rw [show wt1 e (iX i) = sw e (fun c : Ix r s => ((iX i, c) : Ln p q r s))
      (fun c => linePos ((iX i, c) : Ln p q r s)) from rfl, h]
    push_cast; rfl
  have colv : ∀ e ∈ P.support, ∀ k, nu2 p q r s μ' (jX k) = ((∑ i, e ((iX i, jX k) : Ln p q r s) : ℕ) : ℚ) := by
    intro e he k
    rw [← monomialRightWeight_eq_weight_sub rightDiagonalActionFormula hw2 e he (jX k)]
    have h := sw_pos_block e (fun a : Ix p q => ((a, jX k) : Ln p q r s)) (fun a => linePos ((a, jX k) : Ln p q r s))
      iX hi (fun a ha => ucol k a ha e he) (fun i => hlp i k)
    rw [show wt2 e (jX k) = sw e (fun a : Ix p q => ((a, jX k) : Ln p q r s))
      (fun a => linePos ((a, jX k) : Ln p q r s)) from rfl, h]
    push_cast; rfl
  obtain ⟨e0, he0⟩ := exists_mem_support hP0
  refine ⟨fun a b hab => ?_, fun c d hcd => ?_, fun e he => ⟨fun i => ?_, fun k => ?_⟩, fun i => ?_, fun k => ?_⟩
  · have hne := ne_of_posC (hmi a b hab)
    have hR := ker_of_hw hw1 (iX a) (iX b) (hmi a b hab)
    rw [leftOffDiagonalActionFormula p q r s _ _ hne, leftRootOperator_eq_signedPolarization _ _ hne (hs1 a b) P,
      gR_pos_block _ _ _ jX hj P (fun c hc => urow a c hc) (fun c hc => urow b c hc) (fun k => hlp a k)] at hR
    rw [bRow_apply']
    exact hR
  · have hne := ne_of_posC (hmj c d hcd)
    have hR := ker_of_hw hw2 (jX c) (jX d) (hmj c d hcd)
    rw [rightOffDiagonalActionFormula p q r s _ _ hne, rightRootOperator_eq_signedPolarization _ _ hne (hs2 c d) P,
      gR_pos_block _ _ _ iX hi P (fun a ha => ucol c a ha) (fun a ha => ucol d a ha) (fun i => hlp i c)] at hR
    rw [bCol_apply']
    exact hR
  · rw [hα i, rowv e he i, Nat.floor_natCast]
  · rw [hβ k, colv e he k, Nat.floor_natCast]
  · rw [hα i, Nat.floor_pos]
    have h := hnu1 i
    rw [rowv e0 he0 i] at h ⊢
    have h' : 0 < ∑ k, e0 ((iX i, jX k) : Ln p q r s) := by exact_mod_cast h
    exact_mod_cast h'
  · rw [hβ k, Nat.floor_pos]
    have h := hnu2 k
    rw [colv e0 he0 k] at h ⊢
    have h' : 0 < ∑ i, e0 ((iX i, jX k) : Ln p q r s) := by exact_mod_cast h
    exact_mod_cast h'

theorem blkHyp_neg (hM : MinHyp p q r s μ μ' P) {m n : ℕ} (iX : Fin m → Ix p q) (jX : Fin n → Ix r s)
    (hi : Function.Injective iX) (hj : Function.Injective jX)
    (hmi : ∀ a b : Fin m, a < b → posC (iX b) (iX a)) (hmj : ∀ c d : Fin n, c < d → posC (jX d) (jX c))
    (hs1 : ∀ (a b : Fin m) (c : Ix r s), linePos ((iX b, c) : Ln p q r s) = linePos ((iX a, c) : Ln p q r s))
    (hs2 : ∀ (c d : Fin n) (a : Ix p q), linePos ((a, jX d) : Ln p q r s) = linePos ((a, jX c) : Ln p q r s))
    (hlp : ∀ i k, linePos ((iX i, jX k) : Ln p q r s) = false)
    (hcol : ∀ (i : Fin m) (c : Ix r s), linePos ((iX i, c) : Ln p q r s) = false → nu2 p q r s μ' c < 0 →
      c ∈ Set.range jX)
    (hrow : ∀ (k : Fin n) (a : Ix p q), linePos ((a, jX k) : Ln p q r s) = false → nu1 p q r s μ a < 0 →
      a ∈ Set.range iX)
    (hnu1 : ∀ i, nu1 p q r s μ (iX i) < 0) (hnu2 : ∀ k, nu2 p q r s μ' (jX k) < 0)
    (α : Fin m → ℕ) (β : Fin n → ℕ) (hα : ∀ i, α i = ⌊-nu1 p q r s μ (iX i)⌋₊)
    (hβ : ∀ k, β k = ⌊-nu2 p q r s μ' (jX k)⌋₊) :
    IsBlockHighestWeight (fun x : Fin m × Fin n => ((iX x.1, jX x.2) : Ln p q r s)) α β P := by
  have hw1 := mem_leftHighestWeight_of_isMinimalJointVector hM
  have hw2 := mem_rightHighestWeight_of_isMinimalJointVector hM
  have hP0 : P ≠ 0 := hM.2.1
  have lpf : ∀ l : Ln p q r s, (linePos l = true ↔ 0 < nu1 p q r s μ l.1) → nu1 p q r s μ l.1 < 0 →
      linePos l = false := by
    intro l h h'
    cases hl : linePos l
    · rfl
    · rw [hl] at h; linarith [h.1 rfl]
  have urow : ∀ i c, c ∉ Set.range jX → NoVar P ((iX i, c) : Ln p q r s) := by
    intro i c hc e he
    by_contra hne
    obtain ⟨-, h2, h3, h4⟩ := pure_of hM he hne
    have hf : linePos ((iX i, c) : Ln p q r s) = false := lpf _ h3 (hnu1 i)
    have hneg : nu2 p q r s μ' c < 0 := by
      rw [hf] at h4
      rcases lt_or_gt_of_ne h2 with h | h
      · exact h
      · exact absurd (h4.2 h) Bool.false_ne_true
    exact hc (hcol i c hf hneg)
  have ucol : ∀ k a, a ∉ Set.range iX → NoVar P ((a, jX k) : Ln p q r s) := by
    intro k a ha e he
    by_contra hne
    obtain ⟨h1, -, h3, h4⟩ := pure_of hM he hne
    have hf : linePos ((a, jX k) : Ln p q r s) = false := by
      cases hl : linePos ((a, jX k) : Ln p q r s)
      · rfl
      · rw [hl] at h4; linarith [h4.1 rfl, hnu2 k]
    have hneg : nu1 p q r s μ a < 0 := by
      rw [hf] at h3
      rcases lt_or_gt_of_ne h1 with h | h
      · exact h
      · exact absurd (h3.2 h) Bool.false_ne_true
    exact ha (hrow k a hf hneg)
  have rowv : ∀ e ∈ P.support, ∀ i, -nu1 p q r s μ (iX i) = ((∑ k, e ((iX i, jX k) : Ln p q r s) : ℕ) : ℚ) := by
    intro e he i
    rw [← monomialLeftWeight_eq_weight_sub leftDiagonalActionFormula hw1 e he (iX i)]
    have h := sw_neg_block e (fun c : Ix r s => ((iX i, c) : Ln p q r s)) (fun c => linePos ((iX i, c) : Ln p q r s))
      jX hj (fun c hc => urow i c hc e he) (fun k => hlp i k)
    rw [show wt1 e (iX i) = sw e (fun c : Ix r s => ((iX i, c) : Ln p q r s))
      (fun c => linePos ((iX i, c) : Ln p q r s)) from rfl, h]
    push_cast; ring
  have colv : ∀ e ∈ P.support, ∀ k, -nu2 p q r s μ' (jX k) = ((∑ i, e ((iX i, jX k) : Ln p q r s) : ℕ) : ℚ) := by
    intro e he k
    rw [← monomialRightWeight_eq_weight_sub rightDiagonalActionFormula hw2 e he (jX k)]
    have h := sw_neg_block e (fun a : Ix p q => ((a, jX k) : Ln p q r s)) (fun a => linePos ((a, jX k) : Ln p q r s))
      iX hi (fun a ha => ucol k a ha e he) (fun i => hlp i k)
    rw [show wt2 e (jX k) = sw e (fun a : Ix p q => ((a, jX k) : Ln p q r s))
      (fun a => linePos ((a, jX k) : Ln p q r s)) from rfl, h]
    push_cast; ring
  obtain ⟨e0, he0⟩ := exists_mem_support hP0
  refine ⟨fun a b hab => ?_, fun c d hcd => ?_, fun e he => ⟨fun i => ?_, fun k => ?_⟩, fun i => ?_, fun k => ?_⟩
  · have hne := ne_of_posC (hmi a b hab)
    have hR := ker_of_hw hw1 (iX b) (iX a) (hmi a b hab)
    rw [leftOffDiagonalActionFormula p q r s _ _ hne, leftRootOperator_eq_signedPolarization _ _ hne (hs1 b a) P,
      gR_neg_block _ _ _ jX hj P (fun c hc => urow b c hc) (fun c hc => urow a c hc) (fun k => hlp b k),
      neg_eq_zero] at hR
    rw [bRow_apply']
    exact hR
  · have hne := ne_of_posC (hmj c d hcd)
    have hR := ker_of_hw hw2 (jX d) (jX c) (hmj c d hcd)
    rw [rightOffDiagonalActionFormula p q r s _ _ hne, rightRootOperator_eq_signedPolarization _ _ hne (hs2 d c) P,
      gR_neg_block _ _ _ iX hi P (fun a ha => ucol d a ha) (fun a ha => ucol c a ha) (fun i => hlp i d),
      neg_eq_zero] at hR
    rw [bCol_apply']
    exact hR
  · rw [hα i, rowv e he i, Nat.floor_natCast]
  · rw [hβ k, colv e he k, Nat.floor_natCast]
  · rw [hα i, Nat.floor_pos]
    have h := hnu1 i
    have h2 := rowv e0 he0 i
    rw [h2]
    have h' : 0 < ∑ k, e0 ((iX i, jX k) : Ln p q r s) := by
      have : (0 : ℚ) < ((∑ k, e0 ((iX i, jX k) : Ln p q r s) : ℕ) : ℚ) := by rw [← h2]; linarith
      exact_mod_cast this
    exact_mod_cast h'
  · rw [hβ k, Nat.floor_pos]
    have h := hnu2 k
    have h2 := colv e0 he0 k
    rw [h2]
    have h' : 0 < ∑ i, e0 ((iX i, jX k) : Ln p q r s) := by
      have : (0 : ℚ) < ((∑ i, e0 ((iX i, jX k) : Ln p q r s) : ℕ) : ℚ) := by rw [← h2]; linarith
      exact_mod_cast this
    exact_mod_cast h'

end Block

end PI.FJMS
