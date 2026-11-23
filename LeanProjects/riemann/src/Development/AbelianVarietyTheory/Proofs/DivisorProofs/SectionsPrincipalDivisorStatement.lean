import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionsPrincipalDivisor
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv
open CategoryTheory AlgebraicGeometry GlobalTheory.Cartier GlobalTheory.Cartier.CartierDiv

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sections_principal_divisor : ∀ (X : Scheme.{0}) [IsIntegral X] (g : X.functionFieldˣ),
    (principal g).sections = Submodule.span Γ(X, ⊤) {(g : X.functionField)⁻¹} := by
  first | exact @GlobalTheory.sections_principal | exact GlobalTheory.sections_principal | (intros; apply GlobalTheory.sections_principal <;> assumption)
