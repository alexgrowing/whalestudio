import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeOperatorOnCocycleMapsCocycleCoboundaryConj
import Development.AbelianVarietyTheory.Definitions.Foundations.IsDCReps
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeOperatorOnCocycleMaps_cocycle_coboundary_conj : ∀ (Γ : Subgroup SL(2, ℤ)) (w : ℕ) (ι : Type) [Fintype ι] (α : Matrix (Fin 2) (Fin 2) ℤ) (δ : ι → Matrix (Fin 2) (Fin 2) ℤ), 0 < α.det → IsDCReps Γ α δ → (∀ z ∈ Z1 Γ w, hk Γ w δ z ∈ Z1 Γ w) ∧ (∀ z ∈ B1 Γ w, hk Γ w δ z ∈ B1 Γ w) ∧ ∀ z, cj (hk Γ w δ z) = hk Γ w δ (cj z) := by
  first | exact @GlobalTheory.HeckeFamilyMatrices.HkC.hk_cocycle_coboundary_conj | exact GlobalTheory.HeckeFamilyMatrices.HkC.hk_cocycle_coboundary_conj | (intros; apply GlobalTheory.HeckeFamilyMatrices.HkC.hk_cocycle_coboundary_conj <;> assumption)
