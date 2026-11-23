import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinBranching.ExtremalFacts
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinBranching.ExtremalFactsProofA
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LHwlineLemmas
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.DetEmbUnitriA

noncomputable section

namespace PI.WGB

open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial

variable {n : ℕ}

theorem emb_cc_A (g : GL (Fin n) ℂ) (i j : Fin n) :
    ((embGL ℂ n (n + 1) rfl g : GL (Fin (n + 1)) ℂ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
      (Fin.castSucc i) (Fin.castSucc j) = g i j := by
  simp [embGL, blkHom, Matrix.reindexAlgEquiv_apply]

theorem emb_cl_A (g : GL (Fin n) ℂ) (i : Fin n) :
    ((embGL ℂ n (n + 1) rfl g : GL (Fin (n + 1)) ℂ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
      (Fin.castSucc i) (Fin.last n) = 0 := by
  simp [embGL, blkHom, Matrix.reindexAlgEquiv_apply]

theorem emb_lc_A (g : GL (Fin n) ℂ) (i : Fin n) :
    ((embGL ℂ n (n + 1) rfl g : GL (Fin (n + 1)) ℂ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
      (Fin.last n) (Fin.castSucc i) = 0 := by
  simp [embGL, blkHom, Matrix.reindexAlgEquiv_apply]

theorem emb_ll_A (g : GL (Fin n) ℂ) :
    ((embGL ℂ n (n + 1) rfl g : GL (Fin (n + 1)) ℂ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
      (Fin.last n) (Fin.last n) = 1 := by
  simp [embGL, blkHom, Matrix.reindexAlgEquiv_apply]

theorem det_emb_unitri_A (g : GL (Fin n) ℂ) (hl : ∀ i j, j < i → g i j = 0) (hd : ∀ i, g i i = 1) :
    Matrix.GeneralLinearGroup.det (embGL ℂ n (n + 1) rfl g) = 1 := by
  first | exact UpperTheory.Reformulated.B.Qe13.det_emb_unitri_A .. | (apply UpperTheory.Reformulated.B.Qe13.det_emb_unitri_A <;> assumption) | (intros; apply UpperTheory.Reformulated.B.Qe13.det_emb_unitri_A <;> assumption) | (apply @UpperTheory.Reformulated.B.Qe13.det_emb_unitri_A <;> assumption) | (intros; apply @UpperTheory.Reformulated.B.Qe13.det_emb_unitri_A <;> assumption) | (apply @UpperTheory.Reformulated.B.Qe13.det_emb_unitri_A <;> first | assumption | infer_instance) | exact @UpperTheory.Reformulated.B.Qe13.det_emb_unitri_A n g hl hd | exact @UpperTheory.Reformulated.B.Qe13.det_emb_unitri_A n g hl | exact @UpperTheory.Reformulated.B.Qe13.det_emb_unitri_A n g | exact @UpperTheory.Reformulated.B.Qe13.det_emb_unitri_A n

theorem eval_rowAct_A {r c : ℕ} (M : Matrix (Fin r) (Fin r) ℂ) (x : Fin r × Fin c → ℂ)
    (f : MvPolynomial (Fin r × Fin c) ℂ) :
    eval x (rowAct ℂ M f) = eval (fun v => ∑ b, M v.1 b * x (b, v.2)) f := by
  have h : (eval x).comp (rowAct ℂ (n := c) M).toRingHom = eval (fun v => ∑ b, M v.1 b * x (b, v.2)) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [rowAct]
    · intro v
      simp [rowAct]
  exact congrArg (fun φ => φ f) h

def elemGL_A (a b : Fin n) (hab : a ≠ b) (t : ℂ) : GL (Fin n) ℂ where
  val := 1 + Matrix.single a b t
  inv := 1 - Matrix.single a b t
  val_inv := by
    have h : Matrix.single a b t * Matrix.single a b t = 0 := by simp [Ne.symm hab]
    rw [add_mul, one_mul, mul_sub, mul_one, h]
    abel
  inv_val := by
    have h : Matrix.single a b t * Matrix.single a b t = 0 := by simp [Ne.symm hab]
    rw [sub_mul, one_mul, mul_add, mul_one, h]
    abel

theorem elemGL_apply_A (a b : Fin n) (hab : a ≠ b) (t : ℂ) (i j : Fin n) :
    ((elemGL_A a b hab t : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) i j =
      (if i = j then 1 else 0) + (if a = i ∧ b = j then t else 0) := by
  show (1 + Matrix.single a b t) i j = _
  rw [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]

theorem fixed_rowOp_A (lam : DomWeight (n + 1)) (mu : DomWeight n) (f : MvPolynomial (Fin (n + 1) × Fin (n + 1)) ℂ)
    (hf : IsFixedW rfl lam mu f) (a b : Fin n) (hab : a < b) (t : ℂ) (x : Fin (n + 1) × Fin (n + 1) → ℂ) :
    eval (lhwline_rowOp (Fin.castSucc a) (Fin.castSucc b) t x) f = eval x f := by
  have hl : ∀ i j, j < i → ((elemGL_A a b hab.ne t : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) i j = 0 := by
    intro i j hji
    rw [elemGL_apply_A, if_neg (ne_of_gt hji), if_neg]
    · simp
    · rintro ⟨rfl, rfl⟩
      exact lt_asymm hab hji
  have hd : ∀ i, ((elemGL_A a b hab.ne t : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) i i = 1 := by
    intro i
    rw [elemGL_apply_A, if_pos rfl, if_neg]
    · simp
    · rintro ⟨rfl, h⟩
      exact hab.ne h.symm
  have hg := hf.1 (elemGL_A a b hab.ne t) hl hd
  unfold sqAct detPow at hg
  rw [det_emb_unitri_A _ hl hd, one_zpow, Units.val_one, one_smul] at hg
  have h2 := congrArg (eval x) hg
  rw [eval_rowAct_A] at h2
  rw [← h2]
  congr 2
  funext v
  obtain ⟨ρ, s⟩ := v
  simp only [Matrix.transpose_apply, Fin.sum_univ_castSucc, lhwline_rowOp]
  induction ρ using Fin.lastCases with
  | last =>
    simp only [emb_cl_A, emb_ll_A, zero_mul, Finset.sum_const_zero, one_mul, zero_add]
    rw [if_neg (Fin.castSucc_lt_last b).ne']
  | cast ρ =>
    simp only [emb_cc_A, emb_lc_A, zero_mul, add_zero, elemGL_apply_A, add_mul, Finset.sum_add_distrib,
      ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_eq' Finset.univ ρ, if_pos (Finset.mem_univ _)]
    by_cases hρ : ρ = b
    · subst hρ
      rw [if_pos rfl]
      rw [Finset.sum_eq_single a]
      · simp
      · intro c _ hc
        rw [if_neg (fun h => hc h.1.symm)]
      · simp
    · rw [if_neg (fun h => hρ (Fin.castSucc_injective _ h))]
      rw [Finset.sum_eq_zero]
      · simp
      · intro c _
        rw [if_neg (fun h => hρ h.2.symm)]

theorem weight_row_A {r c : ℕ} (m : Fin r × Fin c →₀ ℕ) (ρ : Fin r) :
    Finsupp.weight (rowW r c) m ρ = ∑ s : Fin c, m (ρ, s) := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply,
    Fintype.sum_prod_type]
  rw [Finset.sum_eq_single ρ]
  · simp [rowW]
  · intro b _ hb
    simp [rowW, Ne.symm hb]
  · simp

theorem coeff_rowAct_diag_A {r c : ℕ} (s : Fin r → ℂ) (f : MvPolynomial (Fin r × Fin c) ℂ)
    (m : Fin r × Fin c →₀ ℕ) :
    coeff m (rowAct ℂ (Matrix.diagonal s) f) = (∏ ρ, s ρ ^ (∑ j : Fin c, m (ρ, j))) * coeff m f := by
  induction f using MvPolynomial.induction_on' with
  | monomial m' k =>
    rw [rowActDiagWeight ℂ r c s _ _ (isWeightedHomogeneous_monomial _ _ _ rfl), coeff_smul, coeff_monomial,
      smul_eq_mul]
    split_ifs with h
    · subst h
      simp only [weight_row_A]
    · simp
  | add p q hp hq =>
    rw [map_add, coeff_add, coeff_add, hp, hq, mul_add]

theorem zpow_two_inj_A (a b : ℤ) (h : (2 : ℂ) ^ a = 2 ^ b) : a = b := by
  have h2 := congrArg (fun z : ℂ => ‖z‖) h
  simp only [norm_zpow] at h2
  have h3 : ‖(2 : ℂ)‖ = 2 := by simp
  rw [h3] at h2
  exact zpow_right_injective₀ (by norm_num : (0:ℝ) < 2) (by norm_num) h2

theorem fixed_rowDeg_A (lam : DomWeight (n + 1)) (mu : DomWeight n) (f : MvPolynomial (Fin (n + 1) × Fin (n + 1)) ℂ)
    (hf : IsFixedW rfl lam mu f) (m : Fin (n + 1) × Fin (n + 1) →₀ ℕ) (hm : m ∈ f.support) (a : Fin n) :
    ((∑ s, m (Fin.castSucc a, s) : ℕ) : ℤ) + lam.detShift = mu.w a := by
  set t : Fin n → ℂˣ := fun j => if j = a then Units.mk0 2 two_ne_zero else 1 with ht
  have hg := hf.2 t
  have hdiag : ((embGL ℂ n (n + 1) rfl (diagGL ℂ n t) : GL (Fin (n + 1)) ℂ) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ).transpose =
      Matrix.diagonal (fun c => if c = Fin.castSucc a then (2 : ℂ) else 1) := by
    ext ρ c
    rw [Matrix.transpose_apply, Matrix.diagonal_apply]
    induction ρ using Fin.lastCases with
    | last =>
      induction c using Fin.lastCases with
      | last => simp [emb_ll_A, (Fin.castSucc_lt_last a).ne']
      | cast c => simp [emb_cl_A, (Fin.castSucc_lt_last c).ne']
    | cast ρ =>
      induction c using Fin.lastCases with
      | last => simp [emb_lc_A, (Fin.castSucc_lt_last ρ).ne]
      | cast c =>
        rw [emb_cc_A]
        simp only [diagGL, Matrix.diagonal_apply, ht, Fin.castSucc_inj]
        by_cases hc : c = ρ
        · subst hc
          by_cases hca : c = a <;> simp [hca]
        · simp [hc, Ne.symm hc]
  have hdet : ((Matrix.GeneralLinearGroup.det (embGL ℂ n (n + 1) rfl (diagGL ℂ n t)) : ℂˣ) : ℂ) = 2 := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, ← Matrix.det_transpose, hdiag, Matrix.det_diagonal,
      Fintype.prod_ite_eq']
  unfold sqAct detPow at hg
  rw [hdiag] at hg
  have hc := congrArg (coeff m) hg
  rw [coeff_smul, coeff_smul, coeff_rowAct_diag_A, smul_eq_mul, smul_eq_mul, Units.val_zpow_eq_zpow_val, hdet]
    at hc
  have hcf : coeff m f ≠ 0 := mem_support_iff.mp hm
  have hprod : (∏ ρ : Fin (n + 1), (if ρ = Fin.castSucc a then (2 : ℂ) else 1) ^ (∑ j, m (ρ, j))) =
      2 ^ (∑ j, m (Fin.castSucc a, j)) := by
    rw [Finset.prod_eq_single (Fin.castSucc a)]
    · simp
    · intro b _ hb
      simp [hb]
    · simp
  have hmu : ((∏ j, t j ^ mu.w j : ℂˣ) : ℂ) = 2 ^ mu.w a := by
    rw [Units.coe_prod, Finset.prod_eq_single a]
    · simp [ht]
    · intro b _ hb
      simp [ht, hb]
    · simp
  rw [hprod, hmu, ← mul_assoc] at hc
  have hc2 := mul_right_cancel₀ hcf hc
  rw [← zpow_natCast, ← zpow_add₀ two_ne_zero] at hc2
  have := zpow_two_inj_A _ _ hc2
  omega

end PI.WGB
