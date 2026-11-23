import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WirtConst
open Matrix GlobalTheory.MatDeriv
open scoped Topology

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.MatDeriv

theorem trace_adjugate_mul_eq_sum_perm' {r : ℕ} (A D : Matrix (Fin r) (Fin r) ℂ) :
    (A.adjugate * D).trace = ∑ σ : Equiv.Perm (Fin r), (Equiv.Perm.sign σ : ℂ) *
      ∑ i, (∏ j ∈ Finset.univ.erase i, A (σ j) j) • D (σ i) i := by
  have h1 : ∀ i, (A.adjugate * D) i i = (A.updateCol i (fun k => D k i)).det := by
    intro i
    rw [← cramer_apply, cramer_eq_adjugate_mulVec]
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
  simp only [Matrix.trace, Matrix.diag, h1, det_apply']
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  congr 1
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
  simp only [updateCol_apply, smul_eq_mul]
  rw [mul_comm]
  congr 1
  refine Finset.prod_congr rfl (fun j hj => ?_)
  rw [if_neg (Finset.ne_of_mem_erase hj)]

theorem hasFDerivAt_det {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {n : ℕ}
    (B : E → Matrix (Fin n) (Fin n) ℂ) (w : E)
    (hB : ∀ a b, DifferentiableAt ℝ (fun w' => B w' a b) w) :
    HasFDerivAt (fun w' => (B w').det)
      (∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : ℂ) •
        ∑ i, (∏ j ∈ Finset.univ.erase i, B w (σ j) j) • fderiv ℝ (fun w' => B w' (σ i) i) w) w := by
  have h2 := HasFDerivAt.sum (u := Finset.univ) (fun σ _ =>
      ((HasFDerivAt.finset_prod (u := Finset.univ) (g := fun i w' => B w' (σ i) i)
        (fun i _ => (hB (σ i) i).hasFDerivAt)).const_smul (Equiv.Perm.sign σ : ℂ)))
  refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun w' => ?_)
  simp only [det_apply', Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Units.smul_def, Int.cast_smul_eq_zsmul]
  simp [zsmul_eq_mul]

theorem jacobi_fderiv_det : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {n : ℕ}
    (B : E → Matrix (Fin n) (Fin n) ℂ) (w : E), (∀ a b, DifferentiableAt ℝ (fun w' => B w' a b) w) →
    DifferentiableAt ℝ (fun w' => (B w').det) w ∧
      ∀ ξ : E, fderiv ℝ (fun w' => (B w').det) w ξ = ((B w).adjugate * dMat B w ξ).trace := by
  intro E _ _ n B w hB
  have h := hasFDerivAt_det B w hB
  refine ⟨h.differentiableAt, fun ξ => ?_⟩
  rw [h.fderiv, trace_adjugate_mul_eq_sum_perm']
  simp [dMat, ContinuousLinearMap.sum_apply, Finset.smul_sum, smul_eq_mul, Finset.mul_sum]

end GlobalTheory.MatDeriv
