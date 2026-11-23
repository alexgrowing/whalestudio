import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.AnalyticDictionaryExpAdditiveSurjectiveLinear
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ArcDictExpZeroSection
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFShiftZeroIff
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.analyticDictionaryExp_additive_surjective_linear : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b) (Λ : GtAn a), (∀ z z', (Λ.ex0 z).IsAdd (Λ.ex0 z') (Λ.ex0 (z + z'))) ∧ Function.Surjective Λ.ex0 ∧ ∀ (x : 𝓞 E) z, @GtAct ℂ _ _ (𝓞 E) _ H.starRing a.D₀ ℂ _ _ _ a.oa x (Λ.ex0 z) (Λ.ex0 (Λ.A.actV x z)) := by
  first | exact @GlobalTheory.ArcPts.ex0_additive_surjective_equivariant | exact GlobalTheory.ArcPts.ex0_additive_surjective_equivariant | (intros; apply GlobalTheory.ArcPts.ex0_additive_surjective_equivariant <;> assumption)
