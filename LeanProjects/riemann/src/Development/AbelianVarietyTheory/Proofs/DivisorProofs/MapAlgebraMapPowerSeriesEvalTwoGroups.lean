import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd

set_option autoImplicit false

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory.QLog

theorem map_algebraMap_powerSeriesEvalTwoGroups : ∀ (R S : Type) [CommRing R] [CommRing S] [Algebra R S] (d : ℕ) (τ : Type)
    (t : MvPowerSeries (Fin d ⊕ Fin d) R) (u v : Fin d → MvPowerSeries τ R),
    (∀ i, constantCoeff (u i) = 0) → (∀ i, constantCoeff (v i) = 0) →
    map (algebraMap R S) (at2 t u v) = at2 (map (algebraMap R S) t) (up S u) (up S v) := by
  intro R S _ _ _ d τ t u v hu hv
  have ha : HasSubst (Sum.elim u v) :=
    hasSubst_of_constantCoeff_zero (fun i => by cases i <;> simp [hu, hv])
  rw [at2, at2, map_subst ha]
  congr 1
  funext i
  cases i <;> rfl

end GlobalTheory.QLog
