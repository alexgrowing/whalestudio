import Mathlib
set_option maxSynthPendingDepth 1

open scoped ContDiff
open MeasureTheory

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

namespace ChangeOfVariablesDegree

variable {n : ℕ}

noncomputable def jacobian (H : (Fin n → ℝ) → Fin n → ℝ) (x : Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun k l => fderiv ℝ H x (Pi.single l 1) k

theorem det_fderiv_eq_det_jacobian (H : (Fin n → ℝ) → Fin n → ℝ) (x : Fin n → ℝ) :
    (fderiv ℝ H x).det = (Matrix.of (jacobian H x)).det := by
  rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix']
  congr 1

theorem jacobian_eq_fderiv_apply (H : (Fin n → ℝ) → Fin n → ℝ) (x : Fin n → ℝ)
    (hd : DifferentiableAt ℝ H x) (k l : Fin n) :
    jacobian H x k l = fderiv ℝ (fun y => H y k) x (Pi.single l 1) := by
  have hd' : HasFDerivAt (fun y => H y k) ((ContinuousLinearMap.proj k).comp (fderiv ℝ H x)) x :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) k).hasFDerivAt.comp x
      hd.hasFDerivAt
  rw [hd'.fderiv]; rfl

noncomputable def detCML : ContinuousMultilinearMap ℝ (fun _ : Fin n => Fin n → ℝ) ℝ :=
  { (Matrix.detRowAlternating : (Fin n → ℝ) [⋀^Fin n]→ₗ[ℝ] ℝ).toMultilinearMap with
    cont := continuous_id.matrix_det }

theorem detCML_apply (M : Fin n → Fin n → ℝ) : detCML M = Matrix.det (Matrix.of M) := rfl

theorem det_update_eq_sum (V : Fin n → Fin n → ℝ) (k : Fin n) (r : Fin n → ℝ) :
    Matrix.det (Matrix.of (Function.update V k r)) =
      ∑ l, r l * Matrix.det (Matrix.of (Function.update V k (Pi.single l 1))) := by
  have hr : r = ∑ l, r l • (Pi.single l 1 : Fin n → ℝ) := by
    ext m; simp [Pi.single_apply]
  conv_lhs => rw [hr]
  change (Matrix.detRowAlternating : (Fin n → ℝ) [⋀^Fin n]→ₗ[ℝ] ℝ).toMultilinearMap.toLinearMap V k
    (∑ l, r l • (Pi.single l 1 : Fin n → ℝ)) = _
  rw [map_sum]
  simp only [map_smul, smul_eq_mul, MultilinearMap.toLinearMap_apply]
  rfl

noncomputable def entriesCLM : ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) →L[ℝ] (Fin n → Fin n → ℝ) :=
  ContinuousLinearMap.pi fun k => ContinuousLinearMap.pi fun l =>
    (ContinuousLinearMap.proj k).comp (ContinuousLinearMap.apply ℝ (Fin n → ℝ) (Pi.single l 1))

noncomputable def killRow (i : Fin n) : (Fin n → Fin n → ℝ) →L[ℝ] (Fin n → Fin n → ℝ) :=
  ContinuousLinearMap.pi fun k => if k = i then 0 else ContinuousLinearMap.proj k

theorem killRow_apply_self (i : Fin n) (M : Fin n → Fin n → ℝ) : killRow i M i = 0 := by
  simp [killRow]

theorem killRow_apply_ne {i k : Fin n} (h : k ≠ i) (M : Fin n → Fin n → ℝ) :
    killRow i M k = M k := by
  simp [killRow, h]

theorem update_eq_killRow (M : Fin n → Fin n → ℝ) (i : Fin n) (c : Fin n → ℝ) :
    Function.update M i c = killRow i M + Pi.single i c := by
  funext k
  by_cases h : k = i
  · subst h; simp [killRow_apply_self]
  · simp [killRow_apply_ne h, h]

noncomputable def cofactorFn (H : (Fin n → ℝ) → Fin n → ℝ) (i j : Fin n) (y : Fin n → ℝ) : ℝ :=
  Matrix.det (Matrix.of (Function.update (jacobian H y) i (Pi.single j 1)))

theorem hasFDerivAt_cofactorFn (H : (Fin n → ℝ) → Fin n → ℝ) (hH : ContDiff ℝ ∞ H)
    (i j : Fin n) (x : Fin n → ℝ) :
    HasFDerivAt (cofactorFn H i j)
      ((detCML.linearDeriv (Function.update (jacobian H x) i (Pi.single j 1))).comp
        ((killRow i).comp (entriesCLM.comp (fderiv ℝ (fderiv ℝ H) x)))) x := by
  have h2 : HasFDerivAt (fderiv ℝ H) (fderiv ℝ (fderiv ℝ H) x) x :=
    ((hH.fderiv_right (m := ∞) le_rfl).differentiable (by simp)).differentiableAt.hasFDerivAt
  have hM : HasFDerivAt
      (fun y => (Function.update (jacobian H y) i (Pi.single j 1) : Fin n → Fin n → ℝ))
      ((killRow i).comp (entriesCLM.comp (fderiv ℝ (fderiv ℝ H) x))) x := by
    have : (fun y => (Function.update (jacobian H y) i (Pi.single j 1) : Fin n → Fin n → ℝ)) =
        fun y => killRow i (entriesCLM (fderiv ℝ H y)) + Pi.single i (Pi.single j 1) := by
      funext y; exact update_eq_killRow _ _ _
    rw [this]
    exact ((killRow i).hasFDerivAt.comp x (entriesCLM.hasFDerivAt.comp x h2)).add_const _
  exact (detCML.hasFDerivAt _).comp x hM

theorem sum_det_symm_eq_zero (A : Fin n → Fin n → ℝ) {i k : Fin n} (hik : i ≠ k)
    (S : Fin n → Fin n → ℝ) (hS : ∀ j l, S j l = S l j) :
    ∑ j, Matrix.det (Matrix.of (Function.update (Function.update A i (Pi.single j 1)) k (S j))) =
      0 := by
  simp_rw [det_update_eq_sum _ k (S _)]
  set T : Fin n → Fin n → ℝ := fun j l =>
    Matrix.det (Matrix.of (Function.update (Function.update A i (Pi.single j 1)) k
      (Pi.single l 1))) with hTdef
  have hT : ∀ j l, T j l = - T l j := by
    intro j l
    have hw : (Function.update (Function.update A i (Pi.single l 1)) k (Pi.single j 1)) =
        (Function.update (Function.update A i (Pi.single j 1)) k (Pi.single l 1)) ∘
          Equiv.swap i k := by
      funext r
      by_cases hri : r = i
      · subst hri; simp [Equiv.swap_apply_left, hik]
      · by_cases hrk : r = k
        · subst hrk; simp [Equiv.swap_apply_right, hik]
        · simp [Equiv.swap_apply_of_ne_of_ne hri hrk, hri, hrk]
    have h1 : T l j = - T j l := by
      show Matrix.det (Matrix.of (Function.update (Function.update A i (Pi.single l 1)) k
        (Pi.single j 1))) = _
      rw [hw]
      exact (Matrix.detRowAlternating : (Fin n → ℝ) [⋀^Fin n]→ₗ[ℝ] ℝ).map_swap
        (Function.update (Function.update A i (Pi.single j 1)) k (Pi.single l 1)) hik
    linarith
  have hX : ∑ j, ∑ l, S j l * T j l = - ∑ j, ∑ l, S j l * T j l := by
    conv_lhs => rw [Finset.sum_comm]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hS l j, hT l j]; ring
  change ∑ j, ∑ l, S j l * T j l = 0
  linarith

theorem sum_fderiv_cofactorFn_eq_zero (H : (Fin n → ℝ) → Fin n → ℝ) (hH : ContDiff ℝ ∞ H) (i : Fin n)
    (x : Fin n → ℝ) :
    ∑ j, fderiv ℝ (cofactorFn H i j) x (Pi.single j 1) = 0 := by
  set D2 := fderiv ℝ (fderiv ℝ H) x with hD2
  have hsym : ∀ v w, D2 v w = D2 w v :=
    (hH.contDiffAt (x := x)).isSymmSndFDerivAt (by simp; exact ENat.LEInfty.out)
  simp_rw [(hasFDerivAt_cofactorFn H hH i _ x).fderiv, ContinuousLinearMap.comp_apply,
    ContinuousMultilinearMap.linearDeriv_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hk : k = i
  · subst hk
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [killRow_apply_self, Function.update_idem]
    exact detCML.map_update_zero _ _
  · simp_rw [killRow_apply_ne hk]
    have := sum_det_symm_eq_zero (jacobian H x) (Ne.symm hk)
      (fun j l => D2 (Pi.single j 1) (Pi.single l 1) k)
      (fun j l => by simp only [hsym (Pi.single j 1)])
    exact this

theorem contDiff_cofactorFn (H : (Fin n → ℝ) → Fin n → ℝ) (hH : ContDiff ℝ ∞ H) (i j : Fin n) :
    ContDiff ℝ ∞ (cofactorFn H i j) := by
  have : cofactorFn H i j =
      fun y => detCML (killRow i (entriesCLM (fderiv ℝ H y)) + Pi.single i (Pi.single j 1)) := by
    funext y; rw [detCML_apply, ← update_eq_killRow]; rfl
  rw [this]
  exact detCML.contDiff.comp (((killRow i).contDiff.comp
    (entriesCLM.contDiff.comp (hH.fderiv_right (m := ∞) le_rfl))).add contDiff_const)

theorem integral_det_fderiv_eq_zero (H : (Fin n → ℝ) → Fin n → ℝ) (hH : ContDiff ℝ ∞ H)
    (i : Fin n) (hi : HasCompactSupport fun x => H x i) : ∫ x, (fderiv ℝ H x).det = 0 := by
  set h : (Fin n → ℝ) → ℝ := fun x => H x i with hh
  have hhs : ContDiff ℝ ∞ h := (contDiff_apply ℝ ℝ i).comp hH
  have hJ : ∀ x j, jacobian H x i j = fderiv ℝ h x (Pi.single j 1) := fun x j =>
    jacobian_eq_fderiv_apply H x ((hH.differentiable (by simp)) x) i j
  have hexp : ∀ x, (fderiv ℝ H x).det =
      ∑ j, cofactorFn H i j x * fderiv ℝ h x (Pi.single j 1) := by
    intro x
    rw [det_fderiv_eq_det_jacobian]
    have := det_update_eq_sum (jacobian H x) i (jacobian H x i)
    rw [Function.update_eq_self] at this
    rw [this]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hJ, mul_comm]; rfl
  have hcof := contDiff_cofactorFn H hH i
  have hcd : ∀ j, Continuous fun x => fderiv ℝ (cofactorFn H i j) x (Pi.single j 1) := fun j =>
    ((hcof j).continuous_fderiv (by simp)).clm_apply continuous_const
  have hhd : ∀ j, Continuous fun x => fderiv ℝ h x (Pi.single j 1) := fun j =>
    (hhs.continuous_fderiv (by simp)).clm_apply continuous_const
  have i1 : ∀ j, Integrable (fun x => fderiv ℝ (cofactorFn H i j) x (Pi.single j 1) * h x) :=
    fun j => ((hcd j).mul hhs.continuous).integrable_of_hasCompactSupport hi.mul_left
  have i2 : ∀ j, Integrable (fun x => cofactorFn H i j x * fderiv ℝ h x (Pi.single j 1)) :=
    fun j => ((hcof j).continuous.mul (hhd j)).integrable_of_hasCompactSupport
      (hi.fderiv_apply (𝕜 := ℝ) (Pi.single j 1)).mul_left
  have i3 : ∀ j, Integrable (fun x => cofactorFn H i j x * h x) :=
    fun j => ((hcof j).continuous.mul hhs.continuous).integrable_of_hasCompactSupport hi.mul_left
  have hibp : ∀ j, ∫ x, cofactorFn H i j x * fderiv ℝ h x (Pi.single j 1) =
      - ∫ x, fderiv ℝ (cofactorFn H i j) x (Pi.single j 1) * h x := fun j =>
    integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (i1 j) (i2 j) (i3 j)
      (fun x _ => ((hcof j).differentiable (by simp)) x)
      (fun x _ => (hhs.differentiable (by simp)) x)
  simp_rw [hexp]
  rw [integral_finsetSum _ fun j _ => i2 j]
  simp_rw [hibp]
  rw [Finset.sum_neg_distrib, ← integral_finsetSum _ fun j _ => i1 j]
  simp_rw [← Finset.sum_mul, sum_fderiv_cofactorFn_eq_zero H hH i, zero_mul, integral_zero, neg_zero]

end ChangeOfVariablesDegree
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
