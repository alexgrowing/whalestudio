import Mathlib
import Formalism.PeriodIntegrals.ClassNumImQ
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.QuadraticDedekindZeta.Development
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.ClassNumImQInt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.QuadraticInvariants.QuadPolyIrreducible

open NumberField

namespace PI.ClassNumImQ.ZetaNonvanishing₂.Loc

variable {d : ℕ} {K : Type} [Field K] [NumberField K] {b : K}

noncomputable def om (hq : QuadData d K b) : 𝓞 K :=
  ⟨(1 + b) / 2, (imag_quadratic_integral_basis d K b hq).1⟩

theorem om_coe (hq : QuadData d K b) : ((om hq : 𝓞 K) : K) = (1 + b) / 2 := rfl

theorem basis (hq : QuadData d K b) (x : 𝓞 K) : ∃ m n : ℤ, x = m + n * om hq := by
  obtain ⟨m, n, h⟩ := (imag_quadratic_integral_basis d K b hq).2 x
  refine ⟨m, n, RingOfIntegers.ext ?_⟩
  rw [h]
  push_cast [om_coe]
  rfl

theorem coeff_unique (hq : QuadData d K b) {m n m' n' : ℤ}
    (h : (m : 𝓞 K) + n * om hq = m' + n' * om hq) : m = m' ∧ n = n' := by
  have hK : (m : K) + n * ((1 + b) / 2) = m' + n' * ((1 + b) / 2) := by
    have h' := congrArg (fun x : 𝓞 K => (x : K)) h
    push_cast [om_coe] at h'
    exact h'
  by_cases hn : n = n'
  · subst hn
    refine ⟨?_, rfl⟩
    exact_mod_cast add_right_cancel hK
  · exfalso
    have hne : ((n : K) - n') ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hn)
    apply PI.UnitaryGroupMassFormula.ClassNumImQInv.b_ne_rat hq ((2 * (m' - m) + n' - n) / (n - n'))
    push_cast
    rw [div_eq_iff hne]
    linear_combination (-2 : K) * hK

noncomputable def bb (hq : QuadData d K b) : 𝓞 K := 2 * om hq - 1

end PI.ClassNumImQ.ZetaNonvanishing₂.Loc
