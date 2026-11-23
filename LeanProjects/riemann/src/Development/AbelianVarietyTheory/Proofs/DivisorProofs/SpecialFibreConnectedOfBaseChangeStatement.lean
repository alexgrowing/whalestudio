import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecialFibreConnectedOfBaseChange
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SpecialFibreUnits
open CategoryTheory Limits AlgebraicGeometry
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.special_fibre_connected_of_base_change : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (φ : V →+* O), IsLocalHom φ → ∀ (X : Scheme.{0}) (s : X ⟶ Spec (.of V)), ConnectedSpace ↑(GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.specialFibre (pullback.snd s (Spec.map (CommRingCat.ofHom φ)))) → ConnectedSpace ↑(GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.specialFibre s) := by
  first | exact @GlobalTheory.FibSurj.fibre_connected_of_base_change | exact GlobalTheory.FibSurj.fibre_connected_of_base_change | (intros; apply GlobalTheory.FibSurj.fibre_connected_of_base_change <;> assumption)
