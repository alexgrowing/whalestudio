import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.E8LB
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Degenerations.ToATotal
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import Development.AbelianVarietyTheory.Definitions.Degenerations.MorAlgSt
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsAbelianSchemeThick
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.SplitRed

theorem splitOver_of_unif : ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → ∀ (D₀ : DegData V₁ (maximalIdeal V₁)) (G₀ : Over (Sp V₁)) [GrpObj G₀] [IsCommMonObj G₀] (A₀ : PolAV (Sp (FractionRing V₁))), Unif (maximalIdeal V₁) D₀ A₀ G₀ → IsSemiAbelian G₀ → GlobalTheory.LN.SplitOver G₀ (maximalIdeal V₁) := by
  intro V₁ _ _ _ _ D₀ G₀ _ _ A₀ U _
  obtain ⟨E, -, -, -, -, hE⟩ := GlobalTheory.gtCoord_isGt V₁ (IsLocalRing.maximalIdeal V₁) D₀.toPre 0 G₀ ⟨U.gt 0⟩
  have key : ∀ J : Ideal V₁, J = IsLocalRing.maximalIdeal V₁ →
      ∀ S : SplitExt (Spec (CommRingCat.of (V₁ ⧸ J))),
        S.IsGt ((Over.pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))).obj G₀) →
        GlobalTheory.LN.SplitOver G₀ (IsLocalRing.maximalIdeal V₁) := by
    rintro J rfl S hS
    exact ⟨S, hS⟩
  exact key _ (pow_one _) E hE

end GlobalTheory.SplitRed
end
