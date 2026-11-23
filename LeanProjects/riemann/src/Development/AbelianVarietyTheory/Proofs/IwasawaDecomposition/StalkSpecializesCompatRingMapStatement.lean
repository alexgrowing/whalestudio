import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StalkSpecializesCompatRingMap
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TraitOrdOfTraitOrdPt
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef GlobalTheory.Cartier
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stalk_specializes_compat_ring_map : ∀ (X : Scheme.{0}) {R W : Type} [CommRing R] [IsLocalRing R] [CommRing W] [IsLocalRing W] (ξ : Sp R ⟶ X) (g : R →+* W) (hs : (spMap g ≫ ξ) (closedPoint W) ⤳ ξ (closedPoint R)) (a : X.presheaf.stalk (ξ (closedPoint R))), (Scheme.stalkClosedPointTo (spMap g ≫ ξ)).hom ((X.presheaf.stalkSpecializes hs).hom a) = g ((Scheme.stalkClosedPointTo ξ).hom a) := by
  first | exact @GlobalTheory.TorRef.stalkClosedPointTo_comp_spMap_specializes | exact GlobalTheory.TorRef.stalkClosedPointTo_comp_spMap_specializes | (intros; apply GlobalTheory.TorRef.stalkClosedPointTo_comp_spMap_specializes <;> assumption)
