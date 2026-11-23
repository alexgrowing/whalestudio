import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedFormsMulClosed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DelAtEqSumDOne
open Set Matrix MeasureTheory Filter Topology
open GlobalTheory.HermFrame
open scoped ComplexOrder ContDiff ComplexConjugate

set_option autoImplicit false

noncomputable section

open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.GoodMetric (coordVec)

namespace GlobalTheory.CxForm

variable {n : ℕ}

theorem differentiableAt_repr_map_toLin' {M : V n → Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ} {v : V n}
    (hM : ∀ i j, DifferentiableAt ℝ (fun w => M w i j) v) (γ : Alt n) (S : Finset (Fin (n + n))) :
    DifferentiableAt ℝ (fun w => (bas n).repr (ExteriorAlgebra.map (Matrix.toLin' (M w)) γ) S) v := by
  induction γ using ExteriorAlgebra.induction generalizing S with
  | algebraMap r =>
    simp only [AlgHom.commutes]
    exact differentiableAt_const _
  | ι x =>
    simp only [ExteriorAlgebra.map_apply_ι]
    let ℓ : (Fin n ⊕ Fin n → ℂ) →ₗ[ℂ] ℂ :=
      Finsupp.lapply S ∘ₗ (bas n).repr.toLinearMap ∘ₗ ExteriorAlgebra.ι ℂ
    have hu : DifferentiableAt ℝ (fun w => Matrix.toLin' (M w) x) v := by
      simp only [Matrix.toLin'_apply]
      refine differentiableAt_pi.2 fun i => ?_
      simp only [mulVec, dotProduct]
      exact DifferentiableAt.fun_sum fun j _ => (hM i j).mul_const _
    exact ((LinearMap.toContinuousLinearMap ℓ).restrictScalars ℝ).differentiableAt.comp v hu
  | mul a b ha hb =>
    have e : (fun w => (bas n).repr (ExteriorAlgebra.map (Matrix.toLin' (M w)) (a * b)) S) = fun w =>
        ∑ p : Finset (Fin (n + n)) × Finset (Fin (n + n)), (bas n).repr (ExteriorAlgebra.map (Matrix.toLin' (M w)) a) p.1 *
          (bas n).repr (ExteriorAlgebra.map (Matrix.toLin' (M w)) b) p.2 * (bas n).repr (bas n p.1 * bas n p.2) S :=
      funext fun w => by rw [map_mul, FormMul.repr_mul]
    rw [e]
    exact DifferentiableAt.fun_sum fun p _ => ((ha p.1).mul (hb p.2)).mul_const _
  | add a b ha hb =>
    simp only [map_add, Finsupp.add_apply]
    exact (ha S).add (hb S)

theorem differentiableAt_repr_pull_fderiv : ∀ {n : ℕ} {φ : ReciprocityTheory.L2DbarEstimates.V n → ReciprocityTheory.L2DbarEstimates.V n}
    {v : ReciprocityTheory.L2DbarEstimates.V n}, ContDiffAt ℂ 2 φ v → ∀ (γ : GlobalTheory.CxForm.Alt n) (S : Finset (Fin (n + n))),
    DifferentiableAt ℝ (fun w => (GlobalTheory.CxForm.bas n).repr (GlobalTheory.CxForm.pull (fderiv ℂ φ w) γ) S) v := by
  intro n φ v h γ S
  have hd : DifferentiableAt ℂ (fderiv ℂ φ) v :=
    (h.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have he (b a : Fin n) : DifferentiableAt ℝ (fun w => fderiv ℂ φ w (coordVec b) a) v :=
    (((EuclideanSpace.proj a : V n →L[ℂ] ℂ).differentiableAt).comp v
      (hd.clm_apply (differentiableAt_const (coordVec b)))).restrictScalars ℝ
  have hc (b a : Fin n) : DifferentiableAt ℝ (fun w => conj (fderiv ℂ φ w (coordVec b) a)) v :=
    Complex.conjCLE.differentiableAt.comp v (he b a)
  refine differentiableAt_repr_map_toLin' (M := fun w => fromBlocks (of fun b a => fderiv ℂ φ w (coordVec b) a) 0 0
    (of fun b a => conj (fderiv ℂ φ w (coordVec b) a))) ?_ γ S
  rintro (i | i) (j | j)
  · simpa only [fromBlocks_apply₁₁, of_apply] using he i j
  · simp only [fromBlocks_apply₁₂, Matrix.zero_apply]; exact differentiableAt_const _
  · simp only [fromBlocks_apply₂₁, Matrix.zero_apply]; exact differentiableAt_const _
  · simpa only [fromBlocks_apply₂₂, of_apply] using hc i j

end GlobalTheory.CxForm
