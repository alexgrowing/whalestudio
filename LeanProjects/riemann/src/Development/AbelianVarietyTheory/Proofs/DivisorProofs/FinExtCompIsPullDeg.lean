import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSemiAbelianUniformisationOfFiniteExtTrans
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.FinExtComp

theorem finExt_comp_isPullDeg : ∀ (R R₀ R₁ : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing R₀] [IsDomain R₀] [IsLocalRing R₀] [CommRing R₁] [IsDomain R₁] [IsLocalRing R₁] (ρ₀ : R →+* R₀) (ρ₁ : R₀ →+* R₁) (D : DegPre R) (D₀ : DegPre R₀) (D₁ : DegPre R₁), FinExt ρ₀ → FinExt ρ₁ → Nonempty (IsPullDeg ρ₀ D D₀) → Nonempty (IsPullDeg ρ₁ D₀ D₁) → FinExt (ρ₁.comp ρ₀) ∧ Nonempty (IsPullDeg (ρ₁.comp ρ₀) D D₁) := by
  intro R R₀ R₁ _ _ _ _ _ _ _ _ _ ρ₀ ρ₁ D D₀ D₁ h₀ h₁ ⟨p⟩ ⟨q⟩
  exact ⟨⟨h₁.1, h₁.2.1.comp h₀.2.1, h₁.2.2.comp h₀.2.2⟩,
    GlobalTheory.PullDegComp.nonempty_isPullDeg_comp h₀.2.1 h₁.2.1 p q⟩

end GlobalTheory.Mum.FinExtComp
