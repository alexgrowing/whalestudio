import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitaryTAct
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrActApply
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg GlobalTheory.SteepMult
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isUnitary_tAct_formT_of_isUnitary : ∀ (R S k : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W] (actW : Mat R S →ₗ[ℂ] Module.End ℂ W)
    (B : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ), IsUnitary actW B → IsUnitary (tAct k actW) (formT k B) := by
  first | exact @GlobalTheory.SteepMult.isUnitary_tAct | exact GlobalTheory.SteepMult.isUnitary_tAct | (intros; apply GlobalTheory.SteepMult.isUnitary_tAct <;> assumption)
