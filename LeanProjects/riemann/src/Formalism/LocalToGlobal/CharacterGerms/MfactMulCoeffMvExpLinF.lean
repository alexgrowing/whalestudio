import Mathlib
import Formalism.IncomingBounds.StatementThmP
import Formalism.IncomingBounds.FlowDegreeBounds.ThmPExp
import Formalism.IncomingBounds.FlowDegreeBounds.Cayley

noncomputable section

open scoped BigOperators
open MvPowerSeries

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds

section ExpLin

variable {K : Type} [Field K] {τ : Type} [Fintype τ]

def linF (lam : τ → K) : MvPowerSeries τ K := ∑ w, lam w • (X w : MvPowerSeries τ K)

theorem constantCoeff_linF (lam : τ → K) : constantCoeff (linF lam) = 0 := by
  simp [linF, MvPowerSeries.smul_eq_C_mul]

theorem pderiv_linF (lam : τ → K) (w : τ) : pderiv K w (linF lam) = C (lam w) := by
  classical
  rw [linF, map_sum]
  simp only [Derivation.map_smul, pderiv_X]
  rw [Finset.sum_eq_single w]
  · simp [MvPowerSeries.smul_eq_C_mul]
  · intro b _ hb
    simp [hb]
  · simp

theorem coeff_linF_pow_step (lam : τ → K) (w : τ) (m : τ →₀ ℕ) (k : ℕ) :
    coeff (m + Finsupp.single w 1) (linF lam ^ (k + 1)) * ((m w : K) + 1)
      = ((k : K) + 1) * lam w * coeff m (linF lam ^ k) := by
  have h := congrArg (coeff m) (Derivation.leibniz_pow (pderiv K w) (linF lam) (k + 1))
  rw [coeff_pderiv, pderiv_linF] at h
  rw [h]
  rw [Nat.add_sub_cancel, smul_eq_mul, map_nsmul, MvPowerSeries.coeff_mul_C, nsmul_eq_mul]
  push_cast
  ring

variable [CharZero K]

private theorem coeff_mvExp_eq_sum_range_degree {K : Type} [Field K] {ρ : Type} (h : MvPowerSeries ρ K) (m : ρ →₀ ℕ) :
    coeff m (Formalism.IncomingBounds.mvExp h) = ∑ k ∈ Finset.range (m.degree + 1), coeff m (h ^ k) / (k.factorial : K) := rfl

private theorem add_single_one_ne_zero {ρ : Type} (m : ρ →₀ ℕ) (w : ρ) : m + Finsupp.single w 1 ≠ 0 := by
  intro h
  have := congrArg (fun f : ρ →₀ ℕ => f w) h
  simp at this

theorem coeff_mvExp_linF_step (lam : τ → K) (w : τ) (m : τ →₀ ℕ) :
    coeff (m + Finsupp.single w 1) (mvExp (linF lam)) * ((m w : K) + 1)
      = lam w * coeff m (mvExp (linF lam)) := by
  rw [coeff_mvExp_eq_sum_range_degree, coeff_mvExp_eq_sum_range_degree, map_add Finsupp.degree, Finsupp.degree_single,
    Finset.sum_range_succ', Finset.mul_sum, add_mul, Finset.sum_mul]
  have h0 : coeff (m + Finsupp.single w 1) (linF lam ^ 0) = 0 := by
    classical
    rw [pow_zero, MvPowerSeries.coeff_one, if_neg (add_single_one_ne_zero m w)]
  rw [h0, zero_div, zero_mul, add_zero]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h3 := coeff_linF_pow_step lam w m j
  have hf : (j.factorial : K) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
  have hj : ((j : K) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero j
  rw [div_mul_eq_mul_div, h3, Nat.factorial_succ, Nat.cast_mul]
  push_cast
  field_simp

theorem coeff_zero_mvExp (h : MvPowerSeries τ K) : coeff 0 (mvExp h) = 1 := by
  rw [coeff_mvExp_eq_sum_range_degree]
  simp

end ExpLin

section Rename

variable {K : Type} [Field K] {σ τ : Type}

end Rename

end Formalism.L2.FormalSeriesBounds
