import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Uniformization.SeriesFrame
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolarisationSectionRatioIntegralThetaFamilStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaExpansionScalarsRatioOddMulStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitExpansionScalarRescaleDegreeOneStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_theta_unit_at_traits : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (m : ℕ), Odd m → ∀ Φ : IntFam (maximalIdeal R) D.toPre (m ^ 2) → SecK C.P.L.L C.α (m ^ 2), (∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W), ∃ u : Wˣ, ∀ F, T.Exp 1 u (Φ F) F) → ∀ F₁ : IntFam (maximalIdeal R) D.toPre 1, ∃ θ : SecK C.P.L.L C.α 1, ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W), ∃ u : Wˣ, T.Exp 1 u θ F₁ := by
  intro R _ _ _ hR D C m hm Φ hΦ F₁
  obtain ⟨θ₀, hθ₀⟩ := GlobalTheory.T.exists_polarisationSection_ratio_integralThetaFamily R hR D C F₁
  obtain ⟨r, t, hr, ht, h⟩ := GlobalTheory.T.thetaExpansionScalars_ratio_odd_mul R hR D C m hm Φ hΦ F₁ θ₀ hθ₀
  have hr' : algebraMap R (FractionRing R) r ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 hr
  refine ⟨ReciprocityTheory.ChartRestriction.G.DVR.SecOps.secScale (scal C.A.A.hom
    (algebraMap R (FractionRing R) t / algebraMap R (FractionRing R) r)) θ₀, fun W _ _ _ T => ?_⟩
  obtain ⟨a, b, v, ha, hb, hE, hv⟩ := h W T
  exact ⟨v, GlobalTheory.T.trait_expansionScalar_rescale_degreeOne R hR D C F₁ θ₀ r t _ hr (div_mul_cancel₀ _ hr') W T a b v ha hb hE hv⟩

end GlobalTheory.Mum
