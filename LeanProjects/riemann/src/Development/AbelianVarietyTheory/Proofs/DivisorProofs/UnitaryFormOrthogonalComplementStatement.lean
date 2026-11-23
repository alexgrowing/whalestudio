import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryFormOrthogonalComplement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrActApply
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg GlobalTheory.SteepMult
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_form_orthogonal_complement : ∀ (R S : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (actW : Mat R S →ₗ[ℂ] Module.End ℂ W) (B : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ), IsUnitary actW B →
    ∀ U : Submodule ℂ W, KStable actW U → KStable actW (U.orthogonalBilin B) ∧ U ⊔ U.orthogonalBilin B = ⊤ := by
  first | exact @GlobalTheory.SteepMult.orthogonal_kstable_compl | exact GlobalTheory.SteepMult.orthogonal_kstable_compl | (intros; apply GlobalTheory.SteepMult.orthogonal_kstable_compl <;> assumption)
