import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalizationModelFiniteExtension
import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.MinSt2
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_normalization_model_finiteExtension : ∀ (k Ω : Type) [CommRing k] [IsNoetherianRing k] [Field Ω] [CharZero Ω] [Algebra k Ω] (M : RatModel k Ω) (Ω' : Type) [Field Ω'] [Algebra Ω Ω'] [Algebra k Ω'] [IsScalarTower k Ω Ω'] [FiniteDimensional Ω Ω'], Geo.Tor.IsNormalScheme M.Z → ∃ (M' : RatModel k Ω') (π : M'.Z ⟶ M.Z), Geo.Tor.IsNormalScheme M'.Z ∧ IsFinite π ∧ M'.pt ≫ π = spMap (algebraMap Ω Ω') ≫ M.pt := by
  first | exact @GlobalTheory.NormCover.exists_normalization_model | exact GlobalTheory.NormCover.exists_normalization_model | (intros; apply GlobalTheory.NormCover.exists_normalization_model <;> assumption)
