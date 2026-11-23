import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiltrationStepFromSectionKernel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrActApply
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg GlobalTheory.SteepMult
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.filtration_step_from_section_kernel : ∀ (R S : ℕ) (M : GKMod R S) (N : Submodule ℂ M.V), KStable M.act N → ∀ (k : ℕ) (i : Fin (k + 1))
    (Ψ : (Fin (k + 1) → NC R S) → N), (∀ g, phiN M.act N 1 (section1 Ψ i g) = 0) →
    phiN M.act N (k + 1) Ψ ∈ filt M.act N k := by
  first | exact @GlobalTheory.PositionRel.position_rel | exact GlobalTheory.PositionRel.position_rel | (intros; apply GlobalTheory.PositionRel.position_rel <;> assumption)
