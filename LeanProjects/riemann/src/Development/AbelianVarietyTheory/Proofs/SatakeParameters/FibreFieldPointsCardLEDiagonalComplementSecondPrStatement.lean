import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FibreFieldPointsCardLEDiagonalComplementSecondPr
import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FibrePointsLEId
open CategoryTheory Limits AlgebraicGeometry
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fibreFieldPointsCardLE_diagonalComplementSecondProjection : ∀ {Z X : Scheme.{0}} (f : Z ⟶ X) [IsFinite f] [Etale f] (n : ℕ), GlobalTheory.EtC.Tr.FibrePointsLE f (n + 1) → GlobalTheory.EtC.Tr.FibrePointsLE (GlobalTheory.EtC.Tr.diagComplHom f) n := by
  first | (exact @GlobalTheory.EtC.Tr.fibrePointsLE_diagComplHom) | (exact GlobalTheory.EtC.Tr.fibrePointsLE_diagComplHom) | (intros; apply GlobalTheory.EtC.Tr.fibrePointsLE_diagComplHom  <;> assumption)
