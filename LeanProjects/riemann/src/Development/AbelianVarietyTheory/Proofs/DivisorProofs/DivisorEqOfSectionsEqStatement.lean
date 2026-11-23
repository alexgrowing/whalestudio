import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivisorEqOfSectionsEq
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv
open CategoryTheory AlgebraicGeometry GlobalTheory.Cartier GlobalTheory.Cartier.CartierDiv

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.divisor_eq_of_sections_eq : ∀ (X : Scheme.{0}) [IsIntegral X] [IsAffine X] (D E : CartierDiv X),
    D.sections = E.sections → D = E := by
  first | exact @GlobalTheory.Cartier.CartierDiv.eq_of_sections_eq | exact GlobalTheory.Cartier.CartierDiv.eq_of_sections_eq | (intros; apply GlobalTheory.Cartier.CartierDiv.eq_of_sections_eq <;> assumption)
