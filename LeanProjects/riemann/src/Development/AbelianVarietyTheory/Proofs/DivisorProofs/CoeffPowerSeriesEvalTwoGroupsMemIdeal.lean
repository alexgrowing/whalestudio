import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory.IdealAt2

theorem coeff_powerSeriesEvalTwoGroups_mem_ideal : ∀ (R : Type) [CommRing R] (d : ℕ) (τ : Type) (I : Ideal R)
    (t : MvPowerSeries (Fin d ⊕ Fin d) R) (u v : Fin d → MvPowerSeries τ R),
    (∀ i, constantCoeff (u i) = 0) → (∀ i, constantCoeff (v i) = 0) →
    (∀ α, coeff α t ∈ I) → ∀ α, coeff α (at2 t u v) ∈ I := by
  intro R _ d τ I t u v hu hv ht α
  have hs : HasSubst (Sum.elim u v) :=
    hasSubst_of_constantCoeff_zero fun s => by cases s <;> simp [hu, hv]
  rw [at2, coeff_subst hs]
  refine finsum_induction (fun x => x ∈ I) I.zero_mem (fun x y hx hy => I.add_mem hx hy) ?_
  intro e
  rw [smul_eq_mul]
  exact I.mul_mem_right _ (ht e)

end GlobalTheory.IdealAt2
