import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionsAddDivisor
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv
open CategoryTheory AlgebraicGeometry GlobalTheory.Cartier GlobalTheory.Cartier.CartierDiv

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sections_add_divisor : ∀ (X : Scheme.{0}) [IsIntegral X] [IsAffine X] (D E : CartierDiv X),
    (D + E).sections = D.sections * E.sections := by
  first | exact @GlobalTheory.Cartier.SecAdd.sections_add | exact GlobalTheory.Cartier.SecAdd.sections_add | (intros; apply GlobalTheory.Cartier.SecAdd.sections_add <;> assumption)
