import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CasimirLowerBoundOnStableSubspace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrActApply
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg GlobalTheory.SteepMult
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.casimir_lower_bound_on_stable_subspace : ∀ (R S : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (actW : Mat R S →ₗ[ℂ] Module.End ℂ W) (B : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ) (c₀ : ℚ), IsKLieAct actW →
    (∀ w, w ∈ ⨆ μ : Ix R S → ℚ, wtSub actW μ) → IsUnitary actW B → ∀ U : Submodule ℂ W, KStable actW U →
    (∀ (ν : Ix R S → ℚ) y, y ∈ U → IsHW actW ν y → c₀ < GlobalTheory.BlockReps.casVal ν) →
    ∀ x ∈ U, x ≠ 0 → (c₀ : ℝ) * (B x x).re < (B x (GlobalTheory.BlockReps.casK actW x)).re := by
  first | exact @GlobalTheory.CasimirBound.casimir_form_gt | exact GlobalTheory.CasimirBound.casimir_form_gt | (intros; apply GlobalTheory.CasimirBound.casimir_form_gt <;> assumption)
