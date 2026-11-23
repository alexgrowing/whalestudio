import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Generic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LocalUnfoldBStatementHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CuspidalExponentialDecay
import ReciprocityTheory.L2DbarEstimates.SkodaWeights.LeviVA
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.DerivDerivNonposOfIsLocalMax
import ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.HoloContDiffAtComplex
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.BigStatementPfA

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology GlobalTheory.Shares
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.LeviFibre

theorem contDiffAt_two_of_eventually {n : ℕ} {f : V n → ℂ} {z0 : V n}
    (h : ∀ᶠ z in 𝓝 z0, DifferentiableAt ℂ f z) : ContDiffAt ℂ 2 f z0 := by
  obtain ⟨U, hU, hUo, hz⟩ := eventually_nhds_iff.1 h
  exact ReciprocityTheory.L2DbarEstimates.C.holo_contDiffAt_complex hUo
    (fun z hz => (hU z hz).differentiableWithinAt) hz 2

theorem sum_wd_mul {n : ℕ} {f : V n → ℂ} {z0 : V n} (h : DifferentiableAt ℂ f z0)
    (ξ : Fin n → ℂ) : ∑ j, wd n j f z0 * ξ j = fderiv ℂ f z0 (WithLp.toLp 2 ξ) := by
  have hξ : (WithLp.toLp 2 ξ : V n) = ∑ j, ξ j • bas n j := by
    conv_lhs => rw [← (EuclideanSpace.basisFun (Fin n) ℂ).sum_repr (WithLp.toLp 2 ξ)]
    simp [bas]
  rw [hξ, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [wd_of_differentiableAt h, map_smul, smul_eq_mul, mul_comm]

theorem fderiv_eq_of_quot {n : ℕ} {f g : V n → ℂ} {z0 v : V n} (hf : DifferentiableAt ℂ f z0)
    (hg : DifferentiableAt ℂ g z0) (h0 : g z0 ≠ 0)
    (h : fderiv ℂ (fun z => f z / g z) z0 v = 0) :
    fderiv ℂ f z0 v = (fderiv ℂ g z0 v / g z0) * f z0 := by
  have hq : DifferentiableAt ℂ (fun z => f z / g z) z0 := by
    simp only [div_eq_mul_inv]
    exact hf.mul (hg.inv h0)
  have hev : f =ᶠ[𝓝 z0] fun z => (f z / g z) * g z := by
    filter_upwards [hg.continuousAt.eventually_ne h0] with z hz
    field_simp
  rw [hev.fderiv_eq, fderiv_fun_mul hq hg]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, h]
  field_simp
  ring

theorem levi_log_sum_eq_zero {n m : ℕ} (z0 : V n) (ξ : Fin n → ℂ) (s : Fin m → V n → ℂ)
    (k0 : Fin m) (hs : ∀ k, ∀ᶠ z in 𝓝 z0, DifferentiableAt ℂ (s k) z) (h0 : s k0 z0 ≠ 0)
    (hq : ∀ k, fderiv ℂ (fun z => s k z / s k0 z) z0 (WithLp.toLp 2 ξ) = 0) :
    leviV n (fun z => ((Real.log (∑ k, ‖s k z‖ ^ 2) : ℝ) : ℂ)) z0 ξ = 0 := by
  have hne : (fun i => s i z0) ≠ 0 := fun h => h0 (congrFun h k0)
  have key := ReciprocityTheory.L2DbarEstimates.H.leviLogNormSq n m s z0 ξ
    (fun k => contDiffAt_two_of_eventually (hs k)) hne
  have hJ : ReciprocityTheory.L2DbarEstimates.H.wJac n m s z0 *ᵥ ξ =
      (fderiv ℂ (s k0) z0 (WithLp.toLp 2 ξ) / s k0 z0) • (fun i => s i z0) := by
    funext i
    have := sum_wd_mul (hs i).self_of_nhds ξ
    rw [fderiv_eq_of_quot (hs i).self_of_nhds (hs k0).self_of_nhds h0 (hq i)] at this
    simpa [ReciprocityTheory.L2DbarEstimates.H.wJac, Matrix.mulVec, dotProduct] using this
  have hP : ReciprocityTheory.L2DbarEstimates.projPerp (fun i => s i z0) *ᵥ (fun i => s i z0) = 0 :=
    ReciprocityTheory.ChartRestriction.G.AR.Up.BigA.projPerp_self _ hne
  rw [hJ, Matrix.mulVec_smul, hP, smul_zero] at key
  simp only [ReciprocityTheory.L2DbarEstimates.sqNorm, Complex.normSq_eq_norm_sq] at key
  rw [key]
  simp

theorem main : ∀ (n : ℕ) (z0 : V n) (ξ : Fin n → ℂ), (∀ (m : ℕ) (s : Fin m → V n → ℂ) (k0 : Fin m), (∀ k, ∀ᶠ z in 𝓝 z0, DifferentiableAt ℂ (s k) z) → s k0 z0 ≠ 0 → (∀ k, fderiv ℂ (fun z => s k z / s k0 z) z0 (WithLp.toLp 2 ξ) = 0) → (leviV n (fun z => ((Real.log (∑ k, ‖s k z‖ ^ 2) : ℝ) : ℂ)) z0 ξ).re = 0) ∧ ∀ g : V n → ℝ, ContDiffAt ℝ 2 g z0 → IsLocalMax g z0 → (leviV n (fun z => ((g z : ℝ) : ℂ)) z0 ξ).re ≤ 0 := by
  intro n z0 ξ
  refine ⟨fun m s k0 hs h0 hq => ?_, fun g hg hmax => ?_⟩
  · rw [levi_log_sum_eq_zero z0 ξ s k0 hs h0 hq, Complex.zero_re]
  · exact ReciprocityTheory.L2DbarEstimates.Y.LocalMaximumSecondDerivative.leviV_re_nonpos_of_isLocalMax hg hmax ξ

end GlobalTheory.LeviFibre
