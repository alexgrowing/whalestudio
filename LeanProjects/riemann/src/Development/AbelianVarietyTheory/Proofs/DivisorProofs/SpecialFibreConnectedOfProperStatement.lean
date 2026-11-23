import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecialFibreConnectedOfProper
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SpecialFibreUnits
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.FormalAlgebraisation
open CategoryTheory Limits AlgebraicGeometry
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.special_fibre_connected_of_proper : GlobalTheory.Published.FormalAlgebraisation.Morphisms → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (Y : Scheme.{0}) (f : Y ⟶ Spec (.of O)), IsProper f → ConnectedSpace ↑Y → ConnectedSpace ↑(GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.specialFibre f) := by
  first | exact @GlobalTheory.AlgConn.connectedSpace_specialFibre_of_morphisms | exact GlobalTheory.AlgConn.connectedSpace_specialFibre_of_morphisms | (intros; apply GlobalTheory.AlgConn.connectedSpace_specialFibre_of_morphisms <;> assumption)
