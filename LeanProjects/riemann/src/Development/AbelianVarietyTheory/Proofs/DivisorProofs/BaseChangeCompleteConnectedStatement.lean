import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeCompleteConnected
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
open CategoryTheory Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.FlatModel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.base_change_complete_connected : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (φ : V →+* O), Function.Injective φ → IsLocalHom φ → ∀ (X : Scheme.{0}) (s : X ⟶ Spec (.of V)) (Xw : X.Opens), IsIntegral X → Flat s → GeomIrr s Xw → ConnectedSpace ↑(pullback s (Spec.map (CommRingCat.ofHom φ))) := by
  first | exact @GlobalTheory.FlatModel.connected_pullback_of_geomIrr | exact GlobalTheory.FlatModel.connected_pullback_of_geomIrr | (intros; apply GlobalTheory.FlatModel.connected_pullback_of_geomIrr <;> assumption)
