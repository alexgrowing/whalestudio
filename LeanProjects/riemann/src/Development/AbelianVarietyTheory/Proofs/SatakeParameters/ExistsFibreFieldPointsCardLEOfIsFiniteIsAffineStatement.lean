import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsFibreFieldPointsCardLEOfIsFiniteIsAffine
import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FibrePointsLEId
open CategoryTheory Limits AlgebraicGeometry
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fibreFieldPointsCardLE_of_isFinite_isAffine : ∀ {Z X : Scheme.{0}} (f : Z ⟶ X) [IsFinite f] [IsAffine X], ∃ n, GlobalTheory.EtC.Tr.FibrePointsLE f n := by
  first | (exact @GlobalTheory.EtC.Tr.finite_fibrePointsLE_of_isAffine) | (exact GlobalTheory.EtC.Tr.finite_fibrePointsLE_of_isAffine) | (intros; apply GlobalTheory.EtC.Tr.finite_fibrePointsLE_of_isAffine  <;> assumption)
