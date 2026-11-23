import Mathlib
import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.RegularHypothesesAndConclusion
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HasAffineChartId
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.QuotientOfAffineChartCoverStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FreeActionAffineChartStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.OrbitAffineNeighbourhoodStatement

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Hypotheses₂
open FreeQuot GlobalTheory.CompanionTheory.FreeQuotProof

theorem FreeQuotientScheme_holds : FreeQuotientScheme := by
  intro S G X _ _ hG hfree horb
  obtain ⟨Y₀, q₀, hfin, hflat, hfp, hsurj, hpb⟩ :=
    GlobalTheory.T.quotient_of_affine_chart_cover _ _ (fun x => by
      obtain ⟨U, hU, hxU⟩ := horb x
      obtain ⟨V, W, hxV, hV, hW, hVW, hinv⟩ :=
        GlobalTheory.T.orbit_affine_neighbourhood G X hG x U hU hxU
      exact ⟨V, hxV,
        GlobalTheory.T.free_action_affine_chart G X hG hfree V W hV hW hVW hinv⟩)
  haveI : IsFinite q₀ := hfin
  haveI : Flat q₀ := hflat
  haveI : LocallyOfFinitePresentation q₀ := hfp
  haveI : Surjective q₀ := hsurj
  have hdesc : ∀ {Z} (g₁ g₂ : Z ⟶ X.left), g₁ ≫ q₀ = g₂ ≫ q₀ → g₁ ≫ X.hom = g₂ ≫ X.hom := by
    intro Z g₁ g₂ hg
    rw [← hpb.lift_fst g₁ g₂ hg]
    conv_rhs => rw [← hpb.lift_snd g₁ g₂ hg]
    simp only [Category.assoc]
    first
      | exact hpb.lift g₁ g₂ hg ≫= ((Over.w _).trans (Over.w _).symm)
      | (simp only [Over.w]; try rfl)
  have key : ∀ {Y : Over S} (q : X ⟶ Y), GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot.IsFppfTorsor G q →
      GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot.IsFppfQuotient G q ∧ GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot.IsFppfTorsor G q := fun _ h => ⟨h.isFppfQuotient, h⟩
  refine ⟨Over.mk (EffectiveEpi.desc q₀ X.hom hdesc),
    Over.homMk q₀ (EffectiveEpi.fac q₀ X.hom hdesc), key _ ?_⟩
  unfold GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot.IsFppfTorsor
  refine ⟨IsPullback.of_map_of_faithful (Over.forget S) hpb, PUnit, fun _ => X.left, fun _ => q₀,
    fun _ => ⟨hflat, hfp⟩, fun y => ?_, fun _ => ⟨𝟙 _, Category.id_comp _⟩⟩
  obtain ⟨z, hz⟩ := hsurj.surj y
  exact ⟨PUnit.unit, z, hz⟩

end GlobalTheory.CompanionTheory.Hypotheses₂
