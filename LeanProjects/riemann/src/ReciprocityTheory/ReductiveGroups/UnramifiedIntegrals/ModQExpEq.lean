import Mathlib
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModDefs
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModBasic
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModEvalSer
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModEvalMF

noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM

namespace ReciprocityTheory.ChartRestriction.L1

theorem IsMF.qExp_eq {k : ℤ} {f : ℍ → ℂ} (hf : IsMF k f) {s : PowerSeries ℂ} (hs : Conv s)
    (h : ∀ τ, ev s (qm 1 τ) = f τ) : qExpansion 1 f = s := by
  have hq : ∀ x : ℂ, 0 < ‖x‖ → ‖x‖ < 1 → ∃ τ : ℍ, qm 1 τ = x := by
    intro x hx0 hx1
    have hx : x ≠ 0 := norm_pos_iff.mp hx0
    refine ⟨⟨Function.Periodic.invQParam 1 x,
      Function.Periodic.im_invQParam_pos_of_norm_lt_one one_pos hx1 hx⟩, ?_⟩
    have h1 := Function.Periodic.qParam_right_inv one_ne_zero hx
    unfold Function.Periodic.qParam at h1
    unfold qm
    simpa using h1
  have hsum : ∀ τ : ℍ, HasSum (fun n => PowerSeries.coeff n (qExpansion 1 f) * qm 1 τ ^ n) (f τ) :=
    fun τ => hf.hasSum τ
  have hconv : Conv (qExpansion 1 f) := by
    intro x hx
    obtain ⟨y, hy⟩ : ∃ y : ℝ, y = (‖x‖ + 1) / 2 := ⟨_, rfl⟩
    have hy0 : 0 < y := by rw [hy]; positivity
    have hy1 : y < 1 := by linarith
    have hxy : ‖x‖ < y := by linarith
    have hyn : ‖(y : ℂ)‖ = y := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hy0]
    obtain ⟨τ, hτ⟩ := hq (y : ℂ) (by rw [hyn]; exact hy0) (by rw [hyn]; exact hy1)
    have hs := hsum τ
    rw [hτ] at hs
    have ht : Filter.Tendsto (fun n => ‖PowerSeries.coeff n (qExpansion 1 f) * (y : ℂ) ^ n‖)
        Filter.atTop (nhds 0) := by
      simpa using hs.summable.tendsto_atTop_zero.norm
    obtain ⟨C, hC⟩ := ht.bddAbove_range
    have hr0 : 0 ≤ ‖x‖ / y := by positivity
    have hr1 : ‖x‖ / y < 1 := (div_lt_one hy0).mpr hxy
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
      ((summable_geometric_of_lt_one hr0 hr1).mul_left C)
    have hb := hC ⟨n, rfl⟩
    have he : ‖PowerSeries.coeff n (qExpansion 1 f)‖ * ‖x‖ ^ n =
        ‖PowerSeries.coeff n (qExpansion 1 f) * (y : ℂ) ^ n‖ * (‖x‖ / y) ^ n := by
      rw [norm_mul, norm_pow, hyn, div_pow]
      field_simp <;> ring
    rw [he]
    exact mul_le_mul_of_nonneg_right hb (by positivity)
  refine eq_of_ev_eq hconv hs fun x hx0 hx1 => ?_
  obtain ⟨τ, rfl⟩ := hq x hx0 hx1
  rw [h τ]
  exact (hsum τ).tsum_eq

end ReciprocityTheory.ChartRestriction.L1
