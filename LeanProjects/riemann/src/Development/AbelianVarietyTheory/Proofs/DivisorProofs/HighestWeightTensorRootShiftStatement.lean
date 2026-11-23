import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HighestWeightTensorRootShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrActApply
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg GlobalTheory.SteepMult
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.highest_weight_tensor_root_shift : ∀ (R S : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (actW : Mat R S →ₗ[ℂ] Module.End ℂ W) (Λ : Ix R S → ℚ) (v : W), IsKLieAct actW →
    (∀ w, w ∈ ⨆ μ : Ix R S → ℚ, wtSub actW μ) → IsHW actW Λ v → GlobalTheory.BlockReps.gen actW v = ⊤ →
    ∀ (ν : Ix R S → ℚ) (y : (Fin 1 → NC R S) → W), IsHW (tAct 1 actW) ν y →
      ∃ a b, ¬ sameBlock a b ∧ ν = GlobalTheory.RealLift.addRoot Λ a b := by
  first | exact @GlobalTheory.SteepMult.hw_tensor_one | exact GlobalTheory.SteepMult.hw_tensor_one | (intros; apply GlobalTheory.SteepMult.hw_tensor_one <;> assumption)
