import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CasimirSectionSumIdentity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrActApply
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg GlobalTheory.SteepMult
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.casimir_section_sum_identity : ∀ (R S k : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W] (actW : Mat R S →ₗ[ℂ] Module.End ℂ W)
    (B : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ), IsUnitary actW B → ∀ Ψ : (Fin k → NC R S) → W,
    ∑ i, ∑ g, ((formT 1 B (section1 Ψ i g) (GlobalTheory.BlockReps.casK (tAct 1 actW) (section1 Ψ i g))).re -
        ((R + S : ℕ) : ℝ) * (formT 1 B (section1 Ψ i g) (section1 Ψ i g)).re -
        (formT 1 B (section1 Ψ i g) (fun h => GlobalTheory.BlockReps.casK actW (section1 Ψ i g h))).re) ≤
      (Fintype.card (NC R S) : ℝ) * ((formT k B Ψ (GlobalTheory.BlockReps.casK (tAct k actW) Ψ)).re -
        (formT k B Ψ (fun g => GlobalTheory.BlockReps.casK actW (Ψ g))).re) := by
  first | exact @GlobalTheory.SteepMult.CasDom.casDom | exact GlobalTheory.SteepMult.CasDom.casDom | (intros; apply GlobalTheory.SteepMult.CasDom.casDom <;> assumption)
