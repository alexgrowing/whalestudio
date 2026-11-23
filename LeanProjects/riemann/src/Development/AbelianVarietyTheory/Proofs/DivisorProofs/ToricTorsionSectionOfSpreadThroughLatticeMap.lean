import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EndOnId
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricTorsionSectionEqTorusPointAtClosedPointFielStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricTorsionPointOfTorusPointAtClosedPointFieldStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusPointSectionAlongSpreadingTraitStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Eq8 GlobalTheory.Poinc.Sep.Spz Classical

theorem GlobalTheory.Poinc.Sep.Spz.torAt_of_spread₂ : ∀ (B : Scheme.{0}) (H : Over B) [GrpObj H] [IsCommMonObj H], IsSemiAbelian H → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], GlobalTheory.Mum.Base V₁ → ∀ (G₁ : Over (Sp V₁)) [GrpObj G₁] [IsCommMonObj G₁], IsSemiAbelian G₁ → ∀ (D₁ : DegData V₁ (maximalIdeal V₁)) (A₁ : PolAV (Sp (FractionRing V₁))) (U₁ : Unif (maximalIdeal V₁) D₁ A₁ G₁) (ξ₁ : Sp V₁ ⟶ B) (β₁ : G₁.left ⟶ H.left), IsGrpPullback G₁ H ξ₁ β₁ → ∀ (V₂ : Type) [CommRing V₂] [IsDomain V₂] [IsLocalRing V₂], GlobalTheory.Mum.Base V₂ → ∀ (G₂ : Over (Sp V₂)) [GrpObj G₂] [IsCommMonObj G₂], IsSemiAbelian G₂ → ∀ (D₂ : DegData V₂ (maximalIdeal V₂)) (A₂ : PolAV (Sp (FractionRing V₂))) (U₂ : Unif (maximalIdeal V₂) D₂ A₂ G₂) (ξ₂ : Sp V₂ ⟶ B) (β₂ : G₂.left ⟶ H.left), IsGrpPullback G₂ H ξ₂ β₂ → ∀ ρ : D₂.toPre.X →+ D₁.toPre.X, Spread₂ H U₁ ξ₁ β₁ U₂ ξ₂ β₂ ρ → ∀ (o : Type) [CommRing o] (s : B ⟶ Sp o) (o₁ : o →+* V₁) (o₂ : o →+* V₂), ξ₁ ≫ s = spMap o₁ → ξ₂ ≫ s = spMap o₂ → ∀ (k : ℕ) (ζ : o), 1 ≤ k → IsUnit (k : o) → ζ ^ k = 1 → ∀ (Wo : B.Opens) (h : Wo.toScheme ⟶ H.left) (ξ₁' : Sp V₁ ⟶ Wo.toScheme) (ξ₂' : Sp V₂ ⟶ Wo.toScheme), h ≫ H.hom = Wo.ι → ξ₁' ≫ Wo.ι = ξ₁ → ξ₂' ≫ Wo.ι = ξ₂ → ∀ (F₁ : Type) [Field F₁] [IsAlgClosed F₁] [Algebra (FractionRing V₁) F₁] (F₂ : Type) [Field F₂] [IsAlgClosed F₂] [Algebra (FractionRing V₂) F₂] (c : D₁.toPre.X →+ ℤ) (x₁ : TFK (R := V₁) F₁ ⟶ A₁.A) (x₂ : TFK (R := V₂) F₂ ⟶ A₂.A), TorAt U₁ F₁ k (algebraMap (FractionRing V₁) F₁ (algebraMap V₁ (FractionRing V₁) (o₁ ζ))) c x₁ → x₁.left ≫ genMap U₁ ≫ β₁ = spMap (algebraMap (FractionRing V₁) F₁) ≫ jK V₁ ≫ ξ₁' ≫ h → x₂ ^ k = 1 → x₂.left ≫ genMap U₂ ≫ β₂ = spMap (algebraMap (FractionRing V₂) F₂) ≫ jK V₂ ≫ ξ₂' ≫ h → TorAt U₂ F₂ k (algebraMap (FractionRing V₂) F₂ (algebraMap V₂ (FractionRing V₂) (o₂ ζ))) (c.comp ρ) x₂ := by
  intro B H _ _ hH V₁ _ _ _ hV₁ G₁ _ _ hG₁ D₁ A₁ U₁ ξ₁ β₁ hβ₁ V₂ _ _ _ hV₂ G₂ _ _ hG₂ D₂ A₂ U₂ ξ₂ β₂ hβ₂ ρ hS o _ s o₁ o₂ hs₁ hs₂ k ζ hk hku hζ Wo h ξ₁' ξ₂' hh h₁ h₂ F₁ _ _ _ F₂ _ _ _ c x₁ x₂ hx₁ hx₁g hx₂ hx₂g
  have hw₁ : o₁ ζ ^ k = 1 := by rw [← map_pow, hζ, map_one]
  have hw₂ : o₂ ζ ^ k = 1 := by rw [← map_pow, hζ, map_one]
  have hA := GlobalTheory.T.toricTorsionSection_eq_torusPoint_at_closedPointField B H V₁ hV₁ G₁ hG₁ D₁ A₁ U₁ ξ₁ β₁ hβ₁ (ξ₁' ≫ h) (by rw [Category.assoc, hh, h₁]) k (o₁ ζ) hk hw₁
    F₁ c x₁ hx₁ hx₁g
  obtain ⟨κ, _, b, hb, Gκ, _, m, hm, τ, z, hτ, hz, he⟩ := GlobalTheory.T.torusPointSection_along_spreadingTrait B H hH V₁ G₁ D₁ A₁ U₁ ξ₁ β₁ V₂ G₂ D₂ A₂ U₂ ξ₂ β₂ ρ
    hS o s o₁ o₂ hs₁ hs₂ k ζ hk hζ Wo h ξ₁' ξ₂' hh h₁ h₂ c hA
  exact GlobalTheory.T.toricTorsionPoint_of_torusPoint_at_closedPointField B H V₂ hV₂ G₂ hG₂ D₂ A₂ U₂ ξ₂ β₂ hβ₂ (ξ₂' ≫ h) (by rw [Category.assoc, hh, h₂]) k (o₂ ζ) hk
    (by simpa using hku.map o₂) hw₂ F₂ (c.comp ρ) x₂ hx₂ hx₂g κ b hb Gκ m hm τ hτ z hz he
