import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionsLocallyGeneratedAffine
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv
open CategoryTheory AlgebraicGeometry GlobalTheory.Cartier GlobalTheory.Cartier.CartierDiv

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sections_locally_generated_affine : ∀ (X : Scheme.{0}) [IsIntegral X] [IsAffine X] (D : CartierDiv X)
    (x : X) (g : X.functionFieldˣ), D.IsEqn x g → ∀ f : X.functionField, RegAt x (f * g) →
    ∃ s : Γ(X, ⊤), x ∈ X.basicOpen s ∧ s • f ∈ D.sections := by
  first | exact @GlobalTheory.Cartier.exists_smul_mem_sections_of_regAt | exact GlobalTheory.Cartier.exists_smul_mem_sections_of_regAt | (intros; apply GlobalTheory.Cartier.exists_smul_mem_sections_of_regAt <;> assumption)
