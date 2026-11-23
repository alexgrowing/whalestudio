import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HighestWeightInRangePlusSubmodule
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrActApply
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg GlobalTheory.SteepMult
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_highestWeight_orthogonal_comap_of_mem_range_sup : ∀ (R S : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (actW : Mat R S →ₗ[ℂ] Module.End ℂ W) (B : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (act : Mat R S →ₗ[ℂ] Module.End ℂ V) (φ : W →ₗ[ℂ] V) (F : Submodule ℂ V) (Λ : Ix R S → ℚ) (w : V),
    IsUnitary actW B → KStable act F → (∀ Z, IsKC Z → ∀ x, φ (actW Z x) = act Z (φ x)) →
    w ∈ LinearMap.range φ ⊔ F → w ∈ hwSub act Λ → w ∉ F →
    ∃ Ψ ∈ (F.comap φ).orthogonalBilin B, Ψ ≠ 0 ∧ Ψ ∈ hwSub actW Λ := by
  first | exact @GlobalTheory.SteepMult.hw_lift_orth | exact GlobalTheory.SteepMult.hw_lift_orth | (intros; apply GlobalTheory.SteepMult.hw_lift_orth <;> assumption)
