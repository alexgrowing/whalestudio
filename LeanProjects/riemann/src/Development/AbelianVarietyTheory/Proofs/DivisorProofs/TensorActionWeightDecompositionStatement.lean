import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorActionWeightDecomposition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrActApply
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg GlobalTheory.SteepMult
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensor_action_weight_decomposition : ∀ (R S k : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W] (actW : Mat R S →ₗ[ℂ] Module.End ℂ W),
    (∀ w, w ∈ ⨆ μ : Ix R S → ℚ, wtSub actW μ) →
    ∀ Ψ : (Fin k → NC R S) → W, Ψ ∈ ⨆ μ : Ix R S → ℚ, wtSub (tAct k actW) μ := by
  first | exact @GlobalTheory.SteepMult.tAct_mem_iSup_wtSub | exact GlobalTheory.SteepMult.tAct_mem_iSup_wtSub | (intros; apply GlobalTheory.SteepMult.tAct_mem_iSup_wtSub <;> assumption)
