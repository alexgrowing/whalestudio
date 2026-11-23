import Mathlib
import Formalism.ThetaSupremumBounds.StatementC

open Finset
open scoped Real

namespace Formalism.DimensionVariation

open Formalism.LatticeIndexTer (ph)

theorem size_at_embedding : SizeAtEmbedding := by
  intro Pl _ r g0 ν n Om Ksq kc Msq Th0sq hh hK hkc hM hT hhh hOm h
  have hf : ∀ τ, Real.log ((Om τ)⁻¹ ^ n τ *
      (Real.exp 1 * (2 * (n τ : ℝ) + 2) ^ (2 * g0) * Real.exp (∑ i, ph (ν τ i)))) =
      ((∑ i, ph (ν τ i)) - (n τ : ℝ) * Real.log (Om τ)) +
        (1 + 2 * (g0 : ℝ) * Real.log (2 * (n τ : ℝ) + 2)) := by
    intro τ
    have h2 : (0 : ℝ) < 2 * n τ + 2 := by positivity
    have h3 := hOm τ
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow, Real.log_inv,
      Real.log_exp, Real.log_exp]
    push_cast; ring
  have hpos : ∀ τ, 0 < (Om τ)⁻¹ ^ n τ *
      (Real.exp 1 * (2 * (n τ : ℝ) + 2) ^ (2 * g0) * Real.exp (∑ i, ph (ν τ i))) := by
    intro τ
    have h3 := hOm τ
    positivity
  have hP : 0 < ∏ τ, ((Om τ)⁻¹ ^ n τ *
      (Real.exp 1 * (2 * (n τ : ℝ) + 2) ^ (2 * g0) * Real.exp (∑ i, ph (ν τ i)))) :=
    Finset.prod_pos (fun τ _ => hpos τ)
  refine le_trans (Real.log_le_log hK h) (le_of_eq ?_)
  rw [Real.log_mul hhh.ne' (by positivity), Real.log_mul (by positivity) hP.ne',
    Real.log_prod (fun τ _ => (hpos τ).ne'), Finset.sum_congr rfl (fun τ _ => hf τ),
    Finset.sum_add_distrib, Real.log_mul (by positivity) hT.ne', Real.log_mul (by positivity) hM.ne',
    Real.log_pow]
  push_cast; ring

theorem period_value : PeriodValue := by
  intro d v rdE A1 Z LL0 p_power_smul_sub_sum logOmK logOm hd hv hrd hZ1 hZ2 hFE hK hOm
  have hs : 0 < Real.sqrt d := Real.sqrt_pos.mpr hd
  have hpi := Real.pi_pos
  have e1 : Real.log (2 / Real.sqrt d) = Real.log 2 - Real.log d / 2 := by
    rw [Real.log_div (by norm_num) hs.ne', Real.log_sqrt hd.le]
  have e2 : Real.log (2 * π) = Real.log 2 + Real.log π := Real.log_mul (by norm_num) hpi.ne'
  have e3 : Real.log (d / π) = Real.log d - Real.log π := Real.log_div hd.ne' hpi.ne'
  have e4 : Real.log (2 * π / Real.sqrt d) = Real.log 2 + Real.log π - Real.log d / 2 := by
    rw [Real.log_div (by positivity) hs.ne', e2, Real.log_sqrt hd.le]
  have e5 : Real.log (π / v) = Real.log π - Real.log v := Real.log_div hpi.ne' hv.ne'
  have e6 : Real.log rdE = Real.log 2 + Real.log v := by
    rw [hrd, Real.log_mul (by norm_num) hv.ne']
  have e7 : Real.log (Real.sqrt d) = Real.log d / 2 := Real.log_sqrt hd.le
  rw [e1] at hZ1; rw [e2] at hZ2; rw [e3] at hFE; rw [e6, e7] at hOm
  rw [e4, e5]
  refine ⟨by linarith, by linarith, by linarith⟩

end Formalism.DimensionVariation
