import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsFiniteExtGeomIntegralLocalization
import Development.AbelianVarietyTheory.Definitions.KeyFormula.GeomIntSelf
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.AtOfNumberField
import Development.AbelianVarietyTheory.Statements.ThetaLevelCharacters.MemThetaLevelCharDimZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_ext_geom_integral_localization : ∀ (K : Type) [Field K] [NumberField K] [Algebra K ℂ] (R : Type) [CommRing R] [Algebra K R] [Algebra.Smooth K R] (p : R →ₐ[K] ℂ), ∃ (k : IntermediateField K ℂ) (e : k ⊗[K] R), FiniteDimensional K k ∧ IsIdempotentElem e ∧ Algebra.TensorProduct.lift k.val p (fun _ _ => Commute.all _ _) e = 1 ∧ GeomInt k (Localization.Away e) := by
  first | exact @GlobalTheory.GeomComp.exists_geomInt_component | exact GlobalTheory.GeomComp.exists_geomInt_component | (intros; apply GlobalTheory.GeomComp.exists_geomInt_component <;> assumption)
