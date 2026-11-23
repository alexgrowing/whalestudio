import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedPointOfValuesInSmallAlgClosed
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.closedPoint_of_values_in_small_algClosed : ∀ (F A R K : Type) [Field F] [NumberField F] [CommRing A] [IsDomain A] [CommRing R] [IsLocalRing R] [Field K] (b : F →+* A), b.EssFiniteType → ∀ ψ : A →+* R, GlobalTheory.TChart.IsComplAt ψ → ∀ (ev : R →+* K) (k₀ : Subfield K), Nonempty (k₀ →+* AlgebraicClosure (ResidueField R)) → (∀ a, ev (ψ a) ∈ k₀) → (∀ r ∈ maximalIdeal R, ev r = 0) ∧ ∀ r, ev r ∈ k₀ := by
  first | exact @GlobalTheory.PointAlg.closed_point_of_values | exact GlobalTheory.PointAlg.closed_point_of_values | (intros; apply GlobalTheory.PointAlg.closed_point_of_values <;> assumption)
