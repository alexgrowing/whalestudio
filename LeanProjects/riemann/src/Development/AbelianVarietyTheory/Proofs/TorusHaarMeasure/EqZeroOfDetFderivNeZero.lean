import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpolationModelInequalities
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
open Filter Topology

namespace GlobalTheory.JacobianIndependence

theorem eq_zero_of_eventually_eval {n : ℕ} (p : MvPolynomial (Fin n) ℂ)
    (a : EuclideanSpace ℂ (Fin n))
    (h : ∀ᶠ w in 𝓝 a, MvPolynomial.eval (fun k => w k) p = 0) : p = 0 := by
  have hc : Continuous (fun x : Fin n → ℂ => (WithLp.toLp 2 x : EuclideanSpace ℂ (Fin n))) :=
    PiLp.continuous_toLp 2 _
  have h1 : ∀ᶠ x in 𝓝 (fun k => a k), MvPolynomial.eval x p = 0 :=
    (hc.tendsto (fun k => a k)).eventually h
  rw [nhds_pi, Filter.Eventually, Filter.mem_pi] at h1
  obtain ⟨I, -, t, ht, hsub⟩ := h1
  refine MvPolynomial.funext_set t (fun i => infinite_of_mem_nhds _ (ht i)) ?_
  intro x hx
  rw [map_zero]
  exact hsub (fun i _ => hx i (Set.mem_univ i))

theorem eq_zero_of_det_fderiv_ne_zero :
    ∀ (n : ℕ) (f : Fin n → V n → ℂ), (∀ k, ∀ᶠ z in nhds (0 : V n), DifferentiableAt ℂ (f k) z) →
      (fderiv ℂ (fun z : V n => (WithLp.toLp 2 fun k => f k z : V n)) 0).det ≠ 0 →
      ∀ p : MvPolynomial (Fin n) ℂ,
        (∀ᶠ z in nhds (0 : V n), MvPolynomial.eval (fun k => f k z) p = 0) → p = 0 := by
  intro n f hf hdet p hp
  set F : V n → V n := fun z : V n => (WithLp.toLp 2 fun k => f k z : V n) with hF
  have hd : ∀ᶠ z in 𝓝 (0 : V n), DifferentiableAt ℂ F z := by
    filter_upwards [Filter.eventually_all.2 hf] with z hz
    exact differentiableAt_euclidean.2 hz
  have ha : AnalyticAt ℂ F 0 := GlobalTheory.SCV.analyticAt_iff_eventually_differentiableAt.2 hd
  have hs : HasStrictFDerivAt F
      (((fderiv ℂ F 0).toContinuousLinearEquivOfDetNeZero hdet : V n ≃L[ℂ] V n) :
        V n →L[ℂ] V n) 0 := by
    rw [ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero]
    exact ha.hasStrictFDerivAt
  refine eq_zero_of_eventually_eval p (F 0) ?_
  rw [← hs.map_nhds_eq_of_equiv, Filter.eventually_map]
  exact hp

end GlobalTheory.JacobianIndependence
