import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CompactSpaceMaximalCompactUnitaryInfinite
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
open GlobalTheory.CuspRep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compactSpace_maximalCompact_unitary_infinite : ∀ (E : Type) [Field E] (a : ℕ), CompactSpace (Kinf E a) := by
  first | exact @GlobalTheory.KinfCompactness.compactSpace_Kinf | exact GlobalTheory.KinfCompactness.compactSpace_Kinf | (intros; apply GlobalTheory.KinfCompactness.compactSpace_Kinf <;> assumption)
