import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.BaseIdealIdeal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeQuotientClosedImmersionIdealSheafStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealSheafLeOfLeOnReductionsJacobsonStatement

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

namespace GlobalTheory.FormalAlg

theorem hom_eq_of_reductions_eq : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), I ≤ Ideal.jacobson ⊥ → ∀ (X Z : Over (Spec (CommRingCat.of R))), IsProper X.hom → IsSeparated Z.hom → ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (b : ∀ e, (Y e).left ⟶ X.left), (∀ e, IsPullback (b e) (Y e).hom X.hom (thick R I e)) → ∀ g g' : X ⟶ Z, (∀ e, b e ≫ g.left = b e ≫ g'.left) → g = g' := by
  intro R _ _ I hI X Z hX hZ Y b hb g g' hg
  have hι : IsClosedImmersion (equalizer.ι g g').left := isClosedImmersion_equalizer_ι_left g g'
  have hN : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  have hle : ∀ e : ℕ, (equalizer.ι g g').left.ker ≤ baseIdeal X.hom (I ^ (e + 1)) := by
    intro e
    rw [← (GlobalTheory.T.baseChange_quotient_closedImmersion_idealSheaf R (I ^ (e + 1)) X.left (Y e).left X.hom (b e) (Y e).hom (hb e)).2.1]
    let c : Over.mk (b e ≫ X.hom) ⟶ X := Over.homMk (b e) rfl
    have hc : c ≫ g = c ≫ g' := by
      ext
      exact hg e
    have h1 : (equalizer.lift c hc).left ≫ (equalizer.ι g g').left = b e := by
      rw [← Over.comp_left, equalizer.lift_ι]
      rfl
    rw [← h1]
    exact Scheme.Hom.le_ker_comp _ _
  have hbot : (equalizer.ι g g').left.ker ≤ ⊥ :=
    GlobalTheory.T.idealSheaf_le_of_le_on_reductions_jacobson R I hI X.left X.hom _ ⊥ inferInstance fun e => (hle e).trans le_sup_right
  have hiso : IsIso (equalizer.ι g g').left :=
    IsClosedImmersion.isIso_iff_ker_eq_bot.2 (le_bot_iff.1 hbot)
  ext
  rw [← cancel_epi (equalizer.ι g g').left, ← Over.comp_left, ← Over.comp_left, equalizer.condition]

end GlobalTheory.FormalAlg
