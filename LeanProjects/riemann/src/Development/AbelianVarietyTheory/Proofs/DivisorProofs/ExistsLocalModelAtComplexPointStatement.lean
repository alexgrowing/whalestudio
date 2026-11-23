import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalModelAtComplexPoint
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_localModel_at_complexPoint : ∀ (A : Type) [CommRing A] [IsDomain A] [Algebra ℂ A] [Algebra.EssFiniteType ℂ A] (ε : A →ₐ[ℂ] ℂ),
  ∃ T : Subring (FractionRing A), IsLocModel (algebraMap ℂ (FractionRing A)) T ∧
    RatRes (algebraMap ℂ (FractionRing A)) T ∧
    ∀ a : A, algebraMap A (FractionRing A) a ∈ T ∧ (ε a = 0 → NonUnit T (algebraMap A (FractionRing A) a)) := by
  first | exact @GlobalTheory.FieldPair.exists_locModel_at_point | exact GlobalTheory.FieldPair.exists_locModel_at_point | (intros; apply GlobalTheory.FieldPair.exists_locModel_at_point <;> assumption)
