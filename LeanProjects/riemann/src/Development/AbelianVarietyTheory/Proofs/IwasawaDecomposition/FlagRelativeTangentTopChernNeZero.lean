import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordProportionality
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric

namespace GlobalTheory.GoodMetric

theorem rootDiscr_ne_zero : ∀ (ι : Type) [Fintype ι] (m : ι → ℕ), rootDiscr m ≠ 0 := by
  intro ι _ m
  unfold rootDiscr
  refine Finset.prod_ne_zero_iff.mpr fun τ _ => Finset.prod_ne_zero_iff.mpr fun j _ =>
    Finset.prod_ne_zero_iff.mpr fun i hi => ?_
  rw [sub_ne_zero]
  intro h
  have h2 := X_injective (σ := Root m) (R := ℝ) h
  simp only [Sigma.mk.injEq, heq_eq_eq, true_and] at h2
  exact (Finset.mem_Iio.mp hi).ne h2.symm

end GlobalTheory.GoodMetric
