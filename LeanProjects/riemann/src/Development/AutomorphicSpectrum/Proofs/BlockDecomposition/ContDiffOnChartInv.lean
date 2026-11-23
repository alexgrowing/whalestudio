import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.EquivariantCalculus.ImportsAlt

noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Calc2 PositivityTheory.RgBcC.Calc2.L

namespace GlobalTheory.CompanionTheory.MatInv

section Norm

attribute [-instance] instTopologicalSpaceMatrix

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
  Matrix.linftyOpNormedSpace

def chart (n : ℕ) : (Fin n → Fin n → ℂ) ≃L[ℝ] Matrix (Fin n) (Fin n) ℂ :=
  (Matrix.ofLinearEquiv ℝ).toContinuousLinearEquiv

theorem contDiffOn_chartInv (n : ℕ) :
    ContDiffOn ℝ ∞ (fun M : Fin n → Fin n → ℂ => (chart n).symm (Ring.inverse (chart n M)))
      {M | IsUnit (chart n M)} := by
  haveI : CompleteSpace (Matrix (Fin n) (Fin n) ℂ) := FiniteDimensional.complete ℝ _
  intro M hM
  obtain ⟨u, hu⟩ := hM
  have h1 : ContDiffAt ℝ ∞ Ring.inverse (GlobalTheory.CompanionTheory.MatInv.chart n M) := by
    rw [← hu]
    exact contDiffAt_ringInverse ℝ u
  exact ((GlobalTheory.CompanionTheory.MatInv.chart n).symm.contDiff.contDiffAt.comp M
    (h1.comp M (GlobalTheory.CompanionTheory.MatInv.chart n).contDiff.contDiffAt)).contDiffWithinAt

end Norm

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem contDiffOn_inv : ∀ {n : ℕ}, ContDiffOn ℝ ∞ (fun x : Mat n => x⁻¹) (GLs n) := by
  intro n
  let A : PositivityTheory.RgTw.Mat n →ₗ[ℝ] (Fin n → Fin n → ℂ) :=
    (Matrix.ofLinearEquiv ℝ).symm.toLinearMap
  let B : (Fin n → Fin n → ℂ) →ₗ[ℝ] PositivityTheory.RgTw.Mat n :=
    (Matrix.ofLinearEquiv ℝ).toLinearMap
  have hA : ContDiff ℝ ∞ A := (LinearMap.toContinuousLinearMap A).contDiff
  have hB : ContDiff ℝ ∞ B := (LinearMap.toContinuousLinearMap B).contDiff
  have key : (fun x : PositivityTheory.RgTw.Mat n => x⁻¹) =
      fun x => B ((GlobalTheory.CompanionTheory.MatInv.chart n).symm (Ring.inverse (GlobalTheory.CompanionTheory.MatInv.chart n (A x)))) := by
    funext x
    rw [Matrix.nonsing_inv_eq_ringInverse]
    rfl
  rw [key]
  refine hB.comp_contDiffOn ((GlobalTheory.CompanionTheory.MatInv.contDiffOn_chartInv n).comp hA.contDiffOn ?_)
  intro x hx
  change IsUnit (x : Matrix (Fin n) (Fin n) ℂ)
  exact (Matrix.isUnit_iff_isUnit_det x).2 (isUnit_iff_ne_zero.2 hx)

end GlobalTheory.CompanionTheory.MatInv
