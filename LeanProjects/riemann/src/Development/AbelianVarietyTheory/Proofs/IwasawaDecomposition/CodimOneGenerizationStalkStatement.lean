import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CodimOneGenerizationStalk
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TraitOrdOfTraitOrdPt
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef GlobalTheory.Cartier
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.codim_one_generization_stalk : ∀ (X : Scheme.{0}) {R : Type} [CommRing R] [IsLocalRing R] (ξ : Sp R ⟶ X) (q : Ideal (X.presheaf.stalk (ξ (closedPoint R)))) [q.IsPrime], q.height = 1 → ∃ (z : X) (hs : z ⤳ ξ (closedPoint R)), ringKrullDim (X.presheaf.stalk z) = 1 ∧ q.map (X.presheaf.stalkSpecializes hs).hom = maximalIdeal (X.presheaf.stalk z) ∧ ∀ (W : Type) [CommRing W] [IsLocalRing W] (g : R →+* W), (maximalIdeal W).comap (g.comp (Scheme.stalkClosedPointTo ξ).hom) = q → (spMap g ≫ ξ) (closedPoint W) = z := by
  first | exact @GlobalTheory.LocalRingGeneralisation.exists_generisation_height_one | exact GlobalTheory.LocalRingGeneralisation.exists_generisation_height_one | (intros; apply GlobalTheory.LocalRingGeneralisation.exists_generisation_height_one <;> assumption)
