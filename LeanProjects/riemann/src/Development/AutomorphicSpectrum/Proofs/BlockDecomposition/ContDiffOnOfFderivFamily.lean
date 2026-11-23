import Mathlib
import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.MirabolicColumnBlock

noncomputable section

open PositivityTheory.jumpWindows
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.SmoothVectors

theorem contDiffOn_of_fderiv_family {E F P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {n : ℕ} {U : Set E} (hU : IsOpen U)
    (o : P → E → F) (S : Set P) (A : Fin n → E → E →L[ℝ] ℝ)
    (hA : ∀ i, ContDiffOn ℝ ∞ (A i) U)
    (h : ∀ v ∈ S, ∃ w : Fin n → P, (∀ i, w i ∈ S) ∧
      ∀ M ∈ U, HasFDerivAt (o v) (∑ i, (A i M).smulRight (o (w i) M)) M) :
    ∀ v ∈ S, ContDiffOn ℝ ∞ (o v) U := by
  have key : ∀ m : ℕ, ∀ v ∈ S, ContDiffOn ℝ m (o v) U := by
    intro m
    induction m with
    | zero =>
      intro v hv
      obtain ⟨w, -, hw⟩ := h v hv
      rw [Nat.cast_zero, contDiffOn_zero]
      exact fun M hM => (hw M hM).continuousAt.continuousWithinAt
    | succ m ih =>
      intro v hv
      obtain ⟨w, hwS, hw⟩ := h v hv
      rw [Nat.cast_succ, contDiffOn_succ_iff_fderiv_of_isOpen hU]
      refine ⟨fun M hM => (hw M hM).differentiableAt.differentiableWithinAt, fun hm => ?_, ?_⟩
      · exact absurd hm (by simp)
      · refine ContDiffOn.congr (f := fun M => ∑ i, (A i M).smulRight (o (w i) M)) ?_
          fun M hM => (hw M hM).fderiv
        exact ContDiffOn.sum fun i _ =>
          (contDiffOn_infty.1 (hA i) m).smulRight (ih (w i) (hwS i))
  intro v hv
  exact contDiffOn_infty.2 fun m => key m v hv

section Chart

variable {ι : Type} [Fintype ι] {a : ℕ}

def mulL : LieI ι a →ₗ[ℝ] LieI ι a →ₗ[ℝ] LieI ι a :=
  LinearMap.mk₂ ℝ (fun P Z => Matrix.of.symm (Matrix.of P * Matrix.of Z))
    (fun P P' Z => by
      change Matrix.of.symm ((Matrix.of P + Matrix.of P') * Matrix.of Z) = _
      rw [add_mul]; rfl)
    (fun c P Z => by
      change Matrix.of.symm ((c • Matrix.of P) * Matrix.of Z) = _
      rw [Matrix.smul_mul]; rfl)
    (fun P Z Z' => by
      change Matrix.of.symm (Matrix.of P * (Matrix.of Z + Matrix.of Z')) = _
      rw [mul_add]; rfl)
    (fun c P Z => by
      change Matrix.of.symm (Matrix.of P * (c • Matrix.of Z)) = _
      rw [Matrix.mul_smul]; rfl)

def mulC : LieI ι a →L[ℝ] LieI ι a →L[ℝ] LieI ι a :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap :
      (LieI ι a →ₗ[ℝ] LieI ι a) ≃ₗ[ℝ] (LieI ι a →L[ℝ] LieI ι a)).toLinearMap ∘ₗ mulL)

def invC (M : LieI ι a) : LieI ι a := Matrix.of.symm (Ring.inverse (Matrix.of M))

section Norm

attribute [-instance] instTopologicalSpaceMatrix

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
  Matrix.linftyOpNormedSpace

def chart : LieI ι a ≃L[ℝ] Matrix (Fin a) (Fin a) (ι → ℂ) :=
  (Matrix.ofLinearEquiv ℝ).toContinuousLinearEquiv

end Norm

end Chart

section Orbit

variable {ι : Type} [Fintype ι] {a : ℕ} {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]

end Orbit

end GlobalTheory.CompanionTheory.SmoothVectors

end
