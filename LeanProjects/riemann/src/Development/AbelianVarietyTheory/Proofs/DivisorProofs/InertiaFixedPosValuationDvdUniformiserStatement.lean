import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertiaFixedPosValuationDvdUniformiser
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertia_fixed_pos_valuation_dvd_uniformiser : ∀ (R K L : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [PerfectField (ResidueField R)] [Field K] [Algebra R K] [IsFractionRing R K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L] (W : ValuationSubring L), IsAbove R K W.toSubring → ∀ π : R, Irreducible π → ∀ y : L, (∀ τ ∈ inertia K W, τ y = y) → y ∈ W.nonunits → y / algebraMap K L (algebraMap R K π) ∈ W := by
  first | exact @GlobalTheory.InertiaUnram.div_uniformiser_mem | exact GlobalTheory.InertiaUnram.div_uniformiser_mem | (intros; apply GlobalTheory.InertiaUnram.div_uniformiser_mem <;> assumption)
