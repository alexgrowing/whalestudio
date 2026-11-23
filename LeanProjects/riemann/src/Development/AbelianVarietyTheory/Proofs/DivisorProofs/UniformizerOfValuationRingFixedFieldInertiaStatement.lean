import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformizerOfValuationRingFixedFieldInertia
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformizer_of_valuationRing_fixedField_inertia : ∀ (R K Ω : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [PerfectField (ResidueField R)] [Field K] [Algebra R K] [IsFractionRing R K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (V : ValuationSubring Ω), IsAbove R K V.toSubring → ∀ π : R, Irreducible π → V.valuation (algebraMap K Ω (algebraMap R K π)) < 1 ∧ ∀ y : IntermediateField.fixedField (inertia K V), V.valuation (y : Ω) < 1 → ∃ z : IntermediateField.fixedField (inertia K V), (z : Ω) ∈ V ∧ y = algebraMap K _ (algebraMap R K π) * z := by
  first | exact @GlobalTheory.InertiaFixedUniformizer.uniformizer_fixedField_inertia | exact GlobalTheory.InertiaFixedUniformizer.uniformizer_fixedField_inertia | (intros; apply GlobalTheory.InertiaFixedUniformizer.uniformizer_fixedField_inertia <;> assumption)
