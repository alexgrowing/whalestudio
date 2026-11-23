import Mathlib
import Formalism.PeriodIntegrals.LocJacTyp

noncomputable section

namespace PI.UnitaryGroupMassFormula.LocJacTyp

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain PI.LocJacTyp

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

theorem q_pos : (0 : ℝ) < ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := by
  have h : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact v.ne_bot
  exact_mod_cast Nat.pos_of_ne_zero h

theorem absV_zero : absV v (0 : Fv F v) = 0 := by
  unfold absV
  simp

theorem absV_pos {x : Fv F v} (hx : x ≠ 0) : 0 < absV v x := by
  have h : Valued.v x ≠ 0 := by simpa using hx
  unfold absV
  rw [dif_neg h]
  exact zpow_pos (q_pos v) _

theorem absV_ne_zero {x : Fv F v} (hx : x ≠ 0) : absV v x ≠ 0 := (absV_pos v hx).ne'

theorem absV_mul (x y : Fv F v) : absV v (x * y) = absV v x * absV v y := by
  by_cases hx : x = 0
  · simp [hx, absV_zero]
  by_cases hy : y = 0
  · simp [hy, absV_zero]
  have h1 : Valued.v x ≠ 0 := by simpa using hx
  have h2 : Valued.v y ≠ 0 := by simpa using hy
  have h3 : Valued.v (x * y) ≠ 0 := by simpa using mul_ne_zero hx hy
  unfold absV
  rw [dif_neg h1, dif_neg h2, dif_neg h3, ← zpow_add₀ (q_pos v).ne', ← toAdd_mul]
  congr 2
  apply WithZero.coe_injective
  rw [WithZero.coe_mul, WithZero.coe_unzero, WithZero.coe_unzero, WithZero.coe_unzero, map_mul]

theorem absV_one : absV v (1 : Fv F v) = 1 := by
  have h : Valued.v (1 : Fv F v) ≠ 0 := by simp
  unfold absV
  rw [dif_neg h]
  have h1 : WithZero.unzero h = 1 := by
    apply WithZero.coe_injective
    rw [WithZero.coe_unzero, map_one, WithZero.coe_one]
  rw [h1, toAdd_one, zpow_zero]

theorem absV_inv (x : Fv F v) : absV v x⁻¹ = (absV v x)⁻¹ := by
  by_cases hx : x = 0
  · simp [hx, absV_zero]
  have h := absV_mul v x x⁻¹
  rw [mul_inv_cancel₀ hx, absV_one] at h
  exact eq_inv_of_mul_eq_one_right h.symm

theorem absV_pow (x : Fv F v) (n : ℕ) : absV v (x ^ n) = absV v x ^ n := by
  induction n with
  | zero => simp [absV_one]
  | succ n ih => rw [pow_succ, absV_mul, ih, pow_succ]

theorem absV_div (x y : Fv F v) : absV v (x / y) = absV v x / absV v y := by
  rw [div_eq_mul_inv, absV_mul, absV_inv, div_eq_mul_inv]

theorem dV_ne_zero : dV v ≠ 0 := by
  unfold dV
  split_ifs with h
  · exact h.choose_spec.1
  · exact one_ne_zero

theorem alp_ne_zero (r : ℕ) (a : Fin (r + 1)) : alp v r a ≠ 0 := by
  unfold alp
  split_ifs
  · exact pow_ne_zero _ (inv_ne_zero (dV_ne_zero v))
  · exact one_ne_zero

theorem alp_last (r : ℕ) : alp v r (Fin.last r) = 1 := by
  unfold alp
  simp

theorem natCast_ne_zero {g : ℕ} (hg : 0 < g) : (g : Fv F v) ≠ 0 := by
  intro h0
  have h1 : algebraMap F (Fv F v) (g : F) = algebraMap F (Fv F v) 0 := by
    rw [map_natCast, map_zero]
    exact h0
  exact (Nat.cast_ne_zero.2 hg.ne') ((algebraMap F (Fv F v)).injective h1)

end PI.UnitaryGroupMassFormula.LocJacTyp
