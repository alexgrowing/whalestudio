import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeneratedModuleFiltrationExhaustive
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrActApply
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg GlobalTheory.SteepMult
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generated_module_filtration_exhaustive : ∀ (R S : ℕ) (M : GKMod R S) (Λ : Ix R S → ℚ) (v : M.V), IsHW M.act Λ v → genSub M.act {v} = ⊤ →
    ∀ w, ∃ k, w ∈ filt M.act (GlobalTheory.BlockReps.gen M.act v) k := by
  first | exact @GlobalTheory.SteepSpan.filt_exhaustive | exact GlobalTheory.SteepSpan.filt_exhaustive | (intros; apply GlobalTheory.SteepSpan.filt_exhaustive <;> assumption)
