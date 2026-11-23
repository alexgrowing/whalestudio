import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HighestWeightModuleUnitaryForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrActApply
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg GlobalTheory.SteepMult
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.highest_weight_module_unitary_form : ∀ (R S : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (actW : Mat R S →ₗ[ℂ] Module.End ℂ W) (Λ : Ix R S → ℚ) (v : W), IsKLieAct actW →
    (∀ w, w ∈ ⨆ μ : Ix R S → ℚ, wtSub actW μ) → IsHW actW Λ v → GlobalTheory.BlockReps.gen actW v = ⊤ →
    ∃ B : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ, IsUnitary actW B := by
  first | exact @GlobalTheory.UnitaryTrick.exists_isUnitary | exact GlobalTheory.UnitaryTrick.exists_isUnitary | (intros; apply GlobalTheory.UnitaryTrick.exists_isUnitary <;> assumption)
