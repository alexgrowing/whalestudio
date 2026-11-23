import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Uniformization.SeriesFrame
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulSecK
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMultiplicationPullbackIntegralFamilyOddStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicationPullbackFamilyNeZeroOddStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMultiplicationPullbackGenericSectionCoverStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExpansionOddMultiplicationPullbackAtTraitStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_mulPull : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (m : ℕ), Odd m → ∀ (F₁ : IntFam (maximalIdeal R) D.toPre 1) (θ₀ : SecK C.P.L.L C.α 1), ∃ (G : IntFam (maximalIdeal R) D.toPre (m ^ 2)) (S : SecK C.P.L.L C.α (m ^ 2)), ((∃ α j, (F₁.f α).f j ≠ 0) → ∃ α j, (G.f α).f j ≠ 0) ∧ ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (a b : W), a ≠ 0 → T.Exp a b θ₀ F₁ → ∃ v : Wˣ, T.Exp a (b * v) S G := by
  intro R _ _ _ hR D C m hm F₁ θ₀
  obtain ⟨G, hG⟩ := GlobalTheory.T.exists_multiplicationPullback_integralFamily_odd R hR D m hm F₁
  obtain ⟨S, hS⟩ := GlobalTheory.T.exists_multiplicationPullback_genericSection_cover R hR D C m hm θ₀
  exact ⟨G, S, GlobalTheory.T.multiplicationPullback_family_ne_zero_odd R hR D m hm F₁ G hG,
    fun W _ _ _ T a b ha h => GlobalTheory.T.expansion_oddMultiplicationPullback_at_trait R hR D C m hm F₁ G θ₀ S hG hS W T a b ha h⟩

end GlobalTheory.Mum
