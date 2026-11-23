import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularOfRegularAtCodimOne
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SpecialFibreUnits
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits GlobalTheory.Cartier
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regular_of_regular_at_codim_one : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X],
  (∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)) →
  ∀ (φ : X.functionField) (x : X),
    (∀ z : X, z ⤳ x → IsDiscreteValuationRing (X.presheaf.stalk z) → RegAt z φ) → RegAt x φ := by
  first | exact @GlobalTheory.Hartogs.regAt_of_forall_dvr | exact GlobalTheory.Hartogs.regAt_of_forall_dvr | (intros; apply GlobalTheory.Hartogs.regAt_of_forall_dvr <;> assumption)
