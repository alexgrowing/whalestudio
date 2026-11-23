import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsResolutionImageSup
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsNonvanishingDense
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MeasureTheory Filter Topology

noncomputable section

namespace ResolutionSupBound

theorem eval_smul_homog {ι : Type*} {f : MvPolynomial ι ℂ} {n : ℕ} (hf : f.IsHomogeneous n) (c : ℂ)
    (z : ι → ℂ) : eval (c • z) f = c ^ n * eval z f := by
  classical
  rw [eval_eq, eval_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun e he => ?_
  have hdeg : e.degree = n := by
    by_contra h
    exact (mem_support_iff.mp he) (hf.coeff_eq_zero h)
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  have hs : e.degree = ∑ i ∈ e.support, e i := rfl
  rw [← hdeg, hs]
  ring

theorem ptNorm_smul {ι : Type*} (m : ConeMetric ℂ ι) {n : ℕ} {f : MvPolynomial ι ℂ} (hf : f.IsHomogeneous n)
    {c : ℂ} (hc : c ≠ 0) (z : ι → ℂ) :
    ptNorm m (RingHom.id ℂ) n f (c • z) = ptNorm m (RingHom.id ℂ) n f z := by
  have hc' : (0 : ℝ) < ‖c‖ ^ n := pow_pos (norm_pos_iff.2 hc) n
  simp only [ptNorm, MvPolynomial.map_id, eval_smul_homog hf, m.smul, norm_mul, norm_pow, mul_pow]
  exact mul_div_mul_left _ _ hc'.ne'

theorem proof (hI : ResolutionImageSup.Statement) (hND : NonvanishingDense.Statement) :
    ResolutionSupBound.Statement := by
  intro D Ω _ _ κ _ d
  obtain ⟨C, hC⟩ := hI D Ω κ d
  refine ⟨C, fun n hn f hf z hz => ?_⟩
  set B := C * (n : ℝ) ^ ((D : ℝ) / 2) * resolutionVolumeL2Complex d n f
  obtain ⟨g, hgJ, hgP⟩ := SetLike.not_le_iff_exists.1 d.R.nondeg
  set S := {w | w ∈ mcPts (ι := GlobalTheory κ) (coordIdeal ℤ d.x) ∧ eval w (map (Int.castRingHom ℂ) g) ≠ 0}
  have hzm : z ∈ mcPts (ι := GlobalTheory κ) (coordIdeal ℤ d.x) := by
    refine ⟨fun _ => ?_, hz.2⟩
    by_contra h
    simp only [not_exists, not_not] at h
    exact hz.1 (funext fun q => h q.2)
  have hzS : z ∈ closure S := hND Unit (GlobalTheory κ) (coordIdeal ℤ d.x) (D + 1) g d.arith hgP hzm
  have key : ∀ w ∈ S, ptNorm d.m (RingHom.id ℂ) n f w ≤ B := by
    rintro w ⟨hw, hwg⟩
    obtain ⟨y, c, hc, hyc⟩ := d.R.surj w hw fun h => hwg (h.2 g hgJ)
    have hy : resPt d y = c () • w := by
      rw [resPt, hyc]
      rfl
    rw [← ptNorm_smul d.m hf (hc ()), ← hy]
    exact hC n hn f hf y
  have hρ : ContinuousAt d.m.ρ z :=
    (d.smooth.continuousOn).continuousAt (isOpen_ne.mem_nhds hz.1)
  have hcont : ContinuousAt (ptNorm d.m (RingHom.id ℂ) n f) z := by
    unfold ptNorm
    simp only [MvPolynomial.map_id]
    exact ((MvPolynomial.continuous_eval f).norm.continuousAt).div (hρ.pow n)
      (pow_pos (d.m.pos z hz.1) n).ne'
  have := mem_closure_iff_nhdsWithin_neBot.1 hzS
  exact le_of_tendsto (hcont.tendsto.mono_left nhdsWithin_le_nhds) (eventually_nhdsWithin_of_forall key)

end ResolutionSupBound

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
