import Mathlib
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.FlatImageOfOverFractionFieldOfValuationRing
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoNormalizationPullbackOfToIntegralClosure

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace GlobalTheory

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry in

theorem _root_.GlobalTheory.over_points_ext_of_injective (S : Scheme.{0}) (G : Over S) [IsSeparated G.hom]
    (W F : Type) [CommRing W] [CommRing F] (φ : W →+* F) (hφ : Function.Injective φ)
    (p : Spec (CommRingCat.of W) ⟶ S) (y y' : Over.mk p ⟶ G)
    (h : (Spec.map (CommRingCat.ofHom φ)) ≫ y.left = (Spec.map (CommRingCat.ofHom φ)) ≫ y'.left) :
    y = y' := by
  let d : Over.mk (Spec.map (CommRingCat.ofHom φ) ≫ p) ⟶ Over.mk p :=
    Over.homMk (Spec.map (CommRingCat.ofHom φ)) rfl
  have hd : d ≫ y = d ≫ y' := by
    ext1
    simpa [d] using h
  let l := equalizer.lift d hd
  have hl : l ≫ equalizer.ι y y' = d := equalizer.lift_ι d hd
  have hfac : l.left ≫ (equalizer.ι y y').left = Spec.map (CommRingCat.ofHom φ) := by
    rw [← Over.comp_left, hl]
    rfl
  have hdom : IsSchemeTheoreticallyDominant (Spec.map (CommRingCat.ofHom φ)) :=
    (_root_.GlobalTheory.schemeDominant_specMap_iff _).2 (by simpa using hφ)
  have hdomι : IsSchemeTheoreticallyDominant (equalizer.ι y y').left :=
    ⟨eq_bot_iff.2 ((Scheme.Hom.le_ker_comp l.left _).trans (by rw [hfac, hdom.ker_eq_bot]))⟩
  have hiso : IsIso (equalizer.ι y y').left :=
    _root_.GlobalTheory.isIso_of_isClosedImmersion_of_schemeDominant _
  ext1
  rw [← cancel_epi (equalizer.ι y y').left, ← Over.comp_left, ← Over.comp_left,
    equalizer.condition]

end GlobalTheory
