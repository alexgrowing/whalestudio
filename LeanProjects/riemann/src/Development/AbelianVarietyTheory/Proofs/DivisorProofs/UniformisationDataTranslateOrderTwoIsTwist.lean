import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapsAtExpLeB
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnifPreCharacterGroupIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianPartIsoOfTwoUniformisationsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsoUniformisationTranslateOrderTwoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationsTranslationPeriodMapsCorrespondStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationPeriodsTranslatedBundleTwistStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.MumCmp

theorem isTwist_of_translate : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G) (g : GtPt D.toPre (𝟙_ (Over (Sp R)))), (∃ z : GtPt D.toPre (𝟙_ (Over (Sp R))), z.IsZero ∧ GtPt.IsAdd g g z) → ∀ a : 𝟙_ (Over (Sp R)) ⟶ G, a ^ 2 = 1 → (∀ (e : ℕ) (ae : Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1))) ⟶ (thickObj R (maximalIdeal R) e G).left), ae ≫ (thickObj R (maximalIdeal R) e G).hom = 𝟙 _ → ae ≫ (fstG (maximalIdeal R) e G).left = thick R (maximalIdeal R) e ≫ a.left → ae ≫ (U.gt e).pG.left = thick R (maximalIdeal R) e ≫ g.b.left ∧ ∀ χ : D.toPre.X, LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ ((U.gt e).t χ) ae) (LB.pullGen D.toPre.P.L _ _ (g.s χ) (thick R (maximalIdeal R) e))) → ∀ (A₂ : PolAV (Sp (FractionRing R))) (D₂ : DegData R (maximalIdeal R)) (U₂ : Unif (maximalIdeal R) D₂ A₂ G), LBIso U₂.LG.L (U.LG.L.pull ((toUnit G ≫ a) * 𝟙 G).left) → GlobalTheory.MumCmp.IsTwist D₂.toPre D.toPre g := by
  intro R _ _ _ hB D A G _ _ hG U g hz a ha hlev A₂ D₂ U₂ hL
  obtain ⟨β, hβm, hβq⟩ := GlobalTheory.T.abelianPart_iso_of_two_uniformisations R hB D A G hG U g hz a ha hlev A₂ D₂ U₂ hL
  obtain ⟨xe, hxe⟩ := GlobalTheory.unifPre_characterGroup_iso R (maximalIdeal R) hB.1 D D₂ A A₂ G hG U.toUnifPre U₂.toUnifPre
  obtain ⟨w, hw, h0⟩ := GlobalTheory.T.exists_iso_uniformisation_translate_orderTwo R hB D A G hG U g hz a ha hlev A₂ D₂ U₂ hL β hβm hβq
  have hc := GlobalTheory.T.uniformisations_translation_period_maps_correspond R hB D A G hG U g hz a ha hlev A₂ D₂ U₂ hL β hβm hβq xe hxe w hw
  exact ⟨β, xe, hβm, hc, w, hw,
    GlobalTheory.T.uniformisation_periods_translatedBundle_twist R hB D A G hG U g hz a ha hlev A₂ D₂ U₂ hL β hβm hβq xe hxe hc w hw h0⟩

end GlobalTheory.MumCmp
