import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecialFibreConnected
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SpecialFibreUnits
open AlgebraicGeometry CategoryTheory GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.special_fibre_connected : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (Y : Scheme.{0}) (f : Y ⟶ Spec (.of O)), IsIntegral Y → (∀ z : Y, IsIntegrallyClosed (Y.presheaf.stalk z)) → IsProper f → Flat f → ConnectedSpace (specialFibre f) := by
  first | exact @GlobalTheory.SpecialConn.connectedSpace_specialFibre | exact GlobalTheory.SpecialConn.connectedSpace_specialFibre | (intros; apply GlobalTheory.SpecialConn.connectedSpace_specialFibre <;> assumption)
