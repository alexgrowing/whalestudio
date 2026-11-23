import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IncludeLInjective
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeightTensorDualRepDualHighestWeightAtEmbedding
import Formalism.GradedWeylDivisibility.FinalB

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

noncomputable section

open scoped Matrix

namespace GlobalTheory.HwEigen

theorem rowAct_transvection_eq_eval (K : Type) [Field K] (n : ℕ) (a b : Fin n) (hab : a ≠ b) (s : K)
    (f : MvPolynomial (Fin n × Fin n) K) :
    Formalism.GradedWeylDivisibility.rowAct K (n := n) (Matrix.transvection a b s)ᵀ f =
      (Formalism.GradedWeylDivisibility.rowGen K a b f).eval (MvPolynomial.C s) := by
  have h : (Polynomial.evalRingHom (MvPolynomial.C s)).comp (Formalism.GradedWeylDivisibility.rowGen K (n := n) a b).toRingHom =
      (Formalism.GradedWeylDivisibility.rowAct K (n := n) (Matrix.transvection a b s)ᵀ).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [Formalism.GradedWeylDivisibility.rowGen, Formalism.GradedWeylDivisibility.rowAct]
    · intro v
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Formalism.GradedWeylDivisibility.rowGen,
        Formalism.GradedWeylDivisibility.rowAct, MvPolynomial.aeval_X, Polynomial.coe_evalRingHom]
      simp [Matrix.transvection, Matrix.transpose_apply, Matrix.add_apply, Matrix.one_apply,
        Matrix.single_apply, add_mul, Finset.sum_add_distrib]
      split_ifs with hv
      · rw [Finset.sum_eq_single a]
        · simp only [hv, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, and_self, if_true]
          exact mul_comm _ _
        · intro c _ hc
          simp [Ne.symm hc]
        · simp
      · simp [Ne.symm hv]
  exact (congrArg (fun φ => φ f) h).symm

end GlobalTheory.HwEigen

namespace GlobalTheory.HwEigen

theorem sqAct_smul' (K : Type) [Field K] (n : ℕ) (lam : DomWeight n) (B : GL (Fin n) K) (c : K)
    (f : MvPolynomial (Fin n × Fin n) K) : sqAct K n lam B (c • f) = c • sqAct K n lam B f := by
  unfold sqAct
  rw [map_smul, smul_comm]

theorem rowDiv_eq_zero_of_fixed (K : Type) [Field K] [Infinite K] (n : ℕ) (a b : Fin n) (hab : a ≠ b)
    (f : MvPolynomial (Fin n × Fin n) K)
    (hfix : ∀ s : K, Formalism.GradedWeylDivisibility.rowAct K (n := n) (Matrix.transvection a b s)ᵀ f = f)
    (k : ℕ) (hk : 1 ≤ k) : Formalism.GradedWeylDivisibility.rowDiv K a b k f = 0 := by
  have hP : Formalism.GradedWeylDivisibility.rowGen K a b f - Polynomial.C f = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    apply Set.infinite_of_injective_forall_mem (f := fun s : K => (MvPolynomial.C s : MvPolynomial (Fin n × Fin n) K))
      (MvPolynomial.C_injective _ _)
    intro s
    simp only [Set.mem_setOf_eq, Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_C]
    rw [← rowAct_transvection_eq_eval K n a b hab s, hfix s, sub_self]
  have h := congrArg (fun p => Polynomial.coeff p k) hP
  simp only [Polynomial.coeff_sub, Polynomial.coeff_C, Polynomial.coeff_zero] at h
  rw [if_neg (by omega), sub_zero] at h
  exact h

theorem mu_eq_of_upper_eigen : ∀ (K : Type) [Field K] [CharZero K] (n : ℕ) (lam0 : DomWeight n) (mu : Fin n → ℤ)
    (f : MvPolynomial (Fin n × Fin n) K), f ∈ nablaSq K n lam0 → f ≠ 0 →
    (∀ B : GL (Fin n) K, (B : Matrix (Fin n) (Fin n) K).BlockTriangular id →
      sqAct K n lam0 B f = (∏ a, (B : Matrix (Fin n) (Fin n) K) a a ^ mu a) • f) → mu = lam0.w := by
  intro K _ _ n lam0 mu f hf hf0 hB
  haveI : Infinite K := inferInstance

  have hkill : ∀ a b : Fin n, a < b → ∀ k : ℕ, 1 ≤ k → Formalism.GradedWeylDivisibility.rowDiv K a b k f = 0 := by
    intro a b hab k hk
    have hne : a ≠ b := ne_of_lt hab
    apply rowDiv_eq_zero_of_fixed K n a b hne f _ k hk
    intro s
    have hdet : (Matrix.transvection a b s).det = 1 := Matrix.det_transvection_of_ne a b hne s
    let B : GL (Fin n) K := Matrix.nonsingInvUnit _ (by rw [hdet]; exact isUnit_one)
    have hBv : (B : Matrix (Fin n) (Fin n) K) = Matrix.transvection a b s := rfl
    have hent : ∀ i j, (B : Matrix (Fin n) (Fin n) K) i j = (if i = j then 1 else 0) + (if a = i ∧ b = j then s else 0) := by
      intro i j
      rw [hBv]
      simp [Matrix.transvection, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
    have htri : (B : Matrix (Fin n) (Fin n) K).BlockTriangular id := by
      intro i j hij
      rw [hent]
      have h1 : i ≠ j := fun h => by subst h; exact lt_irrefl _ hij
      have h2 : ¬ (a = i ∧ b = j) := by
        rintro ⟨rfl, rfl⟩
        exact lt_asymm hab hij
      simp [h1, h2]
    have hdiag : ∀ i, (B : Matrix (Fin n) (Fin n) K) i i = 1 := by
      intro i
      rw [hent]
      have h2 : ¬ (a = i ∧ b = i) := by
        rintro ⟨rfl, h⟩
        exact hne h.symm
      simp [h2]
    have h := hB B htri
    simp only [hdiag, one_zpow, Finset.prod_const_one, one_smul] at h
    have hdp : detPow K n B lam0.detShift = 1 := by
      unfold detPow
      have : Matrix.GeneralLinearGroup.det B = 1 := by
        ext
        simp [Matrix.GeneralLinearGroup.val_det_apply, hBv, hdet]
      rw [this, one_zpow, Units.val_one]
    unfold sqAct at h
    rw [hdp, one_smul, hBv] at h
    exact h

  obtain ⟨c, hc⟩ := Formalism.GradedWeylDivisibility.hwLine K n n le_rfl lam0.natW (PI.WGB.natW_anti_A lam0) f hf hkill
  have he : extremal K n lam0 ≠ 0 := Formalism.GradedWeylDivisibility.hwNe K n n le_rfl lam0.natW
  have hce : f = c • extremal K n lam0 := hc
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hf0 (by rw [hce, zero_smul])

  funext i
  let d : Fin n → K := Function.update (fun _ => 1) i 2
  have hdd : (Matrix.diagonal d).det = 2 := by
    rw [Matrix.det_diagonal, Finset.prod_eq_single i]
    · simp [d]
    · intro j _ hj
      simp [d, hj]
    · simp
  let B : GL (Fin n) K := Matrix.nonsingInvUnit _ (by rw [hdd]; exact isUnit_iff_ne_zero.mpr two_ne_zero)
  have hBv : (B : Matrix (Fin n) (Fin n) K) = Matrix.diagonal d := rfl
  have htri : (B : Matrix (Fin n) (Fin n) K).BlockTriangular id := by
    rw [hBv]; exact Matrix.blockTriangular_diagonal d
  have h := hB B htri
  rw [hce, sqAct_smul', GlobalTheory.AlgWtF.DDHw.sqAct_upper K n lam0 B htri, smul_smul, smul_smul] at h
  have h2 := smul_left_injective K he h
  have hprod : ∀ m : Fin n → ℤ, (∏ a, (B : Matrix (Fin n) (Fin n) K) a a ^ m a) = (2 : K) ^ m i := by
    intro m
    rw [Finset.prod_eq_single i]
    · simp [hBv, d]
    · intro j _ hj
      simp [hBv, d, hj]
    · simp
  simp only [hprod] at h2
  have h3 : ((2 : K) ^ lam0.w i) = (2 : K) ^ mu i := by
    have := h2
    rw [mul_comm] at this
    exact (mul_right_cancel₀ hc0 this)
  have h4 : (((2 : ℚ) ^ lam0.w i : ℚ) : K) = (((2 : ℚ) ^ mu i : ℚ) : K) := by
    rw [Rat.cast_zpow, Rat.cast_zpow, Rat.cast_ofNat]
    exact h3
  have h5 := Rat.cast_injective h4
  exact (zpow_right_injective₀ (by norm_num : (0 : ℚ) < 2) (by norm_num) h5).symm

end GlobalTheory.HwEigen
