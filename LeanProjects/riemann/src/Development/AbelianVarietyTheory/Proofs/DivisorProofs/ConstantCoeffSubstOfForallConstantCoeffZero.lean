import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory

theorem constantCoeff_subst_of_constantCoeff_zero :
    ∀ (R : Type) [CommRing R] (σ τ : Type) [Finite σ] (a : σ → MvPowerSeries τ R),
      (∀ i, constantCoeff (a i) = 0) → ∀ g : MvPowerSeries σ R,
        constantCoeff (subst a g) = constantCoeff g := by
  intro R _ σ τ _ a h g
  have ha : HasSubst a := hasSubst_of_constantCoeff_zero h
  have e : g = MvPowerSeries.C (constantCoeff g) + (g - MvPowerSeries.C (constantCoeff g)) := by ring
  conv_lhs => rw [e]
  rw [subst_add ha, map_add, subst_C,
    constantCoeff_subst_eq_zero ha h (f := g - MvPowerSeries.C (constantCoeff g)) (by simp)]
  simp

end GlobalTheory
