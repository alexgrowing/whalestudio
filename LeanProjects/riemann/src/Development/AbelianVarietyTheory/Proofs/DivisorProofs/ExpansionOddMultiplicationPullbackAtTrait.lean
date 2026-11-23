import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Uniformization.SeriesFrame
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulSecK
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntFamPull
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionFrameIsUnitAlongSection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionPullbackCommutingEndomorphismGeneraStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicationPullbackTraitGenericConditionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicationPullbacksDifferByUnitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExpansionMultiplicationPullbackTraitDegreeOneStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exp_mulPull_trait : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (m : ℕ), Odd m → ∀ (F₁ : IntFam (maximalIdeal R) D.toPre 1) (G : IntFam (maximalIdeal R) D.toPre (m ^ 2)) (θ₀ : SecK C.P.L.L C.α 1) (S : SecK C.P.L.L C.α (m ^ 2)), MulFam m F₁ G → MulSecK C m θ₀ S → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (a b : W), a ≠ 0 → T.Exp a b θ₀ F₁ → ∃ v : Wˣ, T.Exp a (b * v) S G := by
  intro R _ _ _ hR D C m hm F₁ G θ₀ S hMF hMS W _ _ _ T a b ha hE
  obtain ⟨σ, ⟨σ', f', hcar, hpull, hexp⟩, hgen⟩ := hE
  obtain ⟨u, hu, hS⟩ := hMS
  obtain ⟨σ₂, hσ₂⟩ := GlobalTheory.T.exists_section_pullback_commuting_endomorphism_generator C.P.L.L C.P.L.isLB T.β (mulA T.G m).left (mulA C.G m).left
    (GlobalTheory.ZH.TorsFrame.mulA_comm T.cart m) 1 (m ^ 2) u hu σ
  have hgen₂ := GlobalTheory.T.multiplicationPullback_trait_genericCondition R D C W T m a u θ₀ S hS σ σ₂ hgen hσ₂
  obtain ⟨G', hG'⟩ := GlobalTheory.Mum.exists_intFam_pull R hR D W T.φ T.D' T.hD T.inj T.loc (m ^ 2) G
  obtain ⟨uG, σ'', huG, hσ'', hexp''⟩ := GlobalTheory.T.expansion_multiplicationPullback_trait_degreeOne R hR D C W T m hm F₁ G hMF σ' f' hpull hexp G'.f hG'
  obtain ⟨v, hv⟩ := GlobalTheory.T.multiplicationPullbacks_differ_by_unit R hR D C W T m u hu uG huG b σ' σ hcar σ₂ σ'' hσ₂ hσ''
  exact ⟨v, σ₂, ⟨σ'', G'.f, hv, hG', hexp''⟩, hgen₂⟩

end GlobalTheory.Mum
