import Mathlib
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshMoll
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshMollB
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.RegularizedMaxC2ExampleRealLine
import GroundTheory.HeightsAndTheta.Heights.Regularisation.IsOpenKappaOpenNeighbourhood
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

namespace ArgumentConvergenceLemmas

open Filter Topology Metric Set MeasureTheory
open scoped ContDiff
open ReciprocityTheory.AnForm.A (Mollifier molli shrink)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (errE errorWithLinear ell)

noncomputable section

theorem molli_contDiffAt {D : ℕ} (ρ : Mollifier D) {P : Set (Fin D → ℂ)} (hP : IsOpen P)
    {u : (Fin D → ℂ) → ℝ} (hu : ContinuousOn u P) {ε : ℝ} (hε : 0 < ε) {z : Fin D → ℂ}
    (hz : z ∈ shrink P ε) : ContDiffAt ℝ ∞ (molli ρ ε u) z := by
  obtain ⟨δ, hδ, hδP⟩ := ReciprocityTheory.AnForm.A.exists_thick hP hε.le hz
  have hi : Integrable ((closedBall z (ε + δ)).indicator u) :=
    (integrable_indicator_iff isClosed_closedBall.measurableSet).2
      ((hu.mono hδP).integrableOn_compact (isCompact_closedBall z (ε + δ)))
  have hg := (ReciprocityTheory.AnForm.A.scaled_hasCompactSupport ρ hε).contDiff_convolution_left
    (ContinuousLinearMap.lsmul ℝ ℝ) (μ := volume) (n := ⊤) (ReciprocityTheory.AnForm.A.scaled_contDiff ρ ε)
    hi.locallyIntegrable
  refine hg.contDiffAt.congr_of_eventuallyEq ?_
  filter_upwards [ball_mem_nhds z hδ] with y hy
  rw [mem_ball] at hy
  rw [ReciprocityTheory.AnForm.A.molli_eq_C ρ hε (C := closedBall z (ε + δ))
    (closedBall_subset_closedBall' (by linarith)), convolution_def]
  rfl

section Calculus

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem norm_fderiv_fderiv_eq (g : E → F) (y : E) :
    ‖fderiv ℝ (fderiv ℝ g) y‖ = ‖iteratedFDeriv ℝ 2 g y‖ := by
  rw [← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv]

theorem norm_iteratedFDeriv_sub_eq {a b : E → ℝ} {V : Set E} (hV : IsOpen V)
    (ha : ContDiffOn ℝ 2 a V) (hb : ContDiffOn ℝ 2 b V) {z : E} (hz : z ∈ V) :
    ‖iteratedFDeriv ℝ 0 (fun y => a y - b y) z‖ = ‖a z - b z‖ ∧
      ‖iteratedFDeriv ℝ 1 (fun y => a y - b y) z‖ = ‖fderiv ℝ a z - fderiv ℝ b z‖ ∧
      ‖iteratedFDeriv ℝ 2 (fun y => a y - b y) z‖ =
        ‖fderiv ℝ (fderiv ℝ a) z - fderiv ℝ (fderiv ℝ b) z‖ := by
  have da : DifferentiableAt ℝ a z :=
    (ha.contDiffAt (hV.mem_nhds hz)).differentiableAt (by norm_num)
  have db : DifferentiableAt ℝ b z :=
    (hb.contDiffAt (hV.mem_nhds hz)).differentiableAt (by norm_num)
  refine ⟨norm_iteratedFDeriv_zero, ?_, ?_⟩
  · rw [norm_iteratedFDeriv_one, fderiv_fun_sub da db]
  · rw [← norm_fderiv_fderiv_eq, fderiv2_sub_of_contDiffOn hV ha hb hz]

theorem norm_iteratedFDeriv_comp_le_of_isOpen {g : F → G} {f : E → F} {s : Set E} {t : Set F}
    (hs : IsOpen s) (ht : IsOpen t) (hg : ContDiffOn ℝ 2 g t) (hf : ContDiffOn ℝ 2 f s)
    (hst : MapsTo f s t) {x : E} (hx : x ∈ s) {n : ℕ} (hn : n ≤ 2) {C d : ℝ}
    (hC : ∀ i : ℕ, i ≤ 2 → ‖iteratedFDeriv ℝ i g (f x)‖ ≤ C)
    (hD : ∀ i : ℕ, 1 ≤ i → i ≤ 2 → ‖iteratedFDeriv ℝ i f x‖ ≤ d ^ i) :
    ‖iteratedFDeriv ℝ n (g ∘ f) x‖ ≤ n.factorial * C * d ^ n := by
  have hn' : (n : WithTop ℕ∞) ≤ 2 := by exact_mod_cast hn
  rw [← iteratedFDerivWithin_of_isOpen n hs hx]
  refine norm_iteratedFDerivWithin_comp_le (hg.of_le hn') (hf.of_le hn') le_rfl ht.uniqueDiffOn
    hs.uniqueDiffOn hst hx (fun i hi => ?_) (fun i hi1 hi => ?_)
  · rw [iteratedFDerivWithin_of_isOpen i ht (hst hx)]
    exact hC i (hi.trans hn)
  · rw [iteratedFDerivWithin_of_isOpen i hs hx]
    exact hD i hi1 (hi.trans hn)

theorem exists_bound_iteratedFDeriv {f : E → F} {s K : Set E} (hs : IsOpen s)
    (hf : ContDiffOn ℝ 2 f s) (hK : IsCompact K) (hKs : K ⊆ s) :
    ∃ B : ℝ, ∀ i : ℕ, i ≤ 2 → ∀ y ∈ K, ‖iteratedFDeriv ℝ i f y‖ ≤ B := by
  have h : ∀ i : ℕ, i ≤ 2 → ∃ B : ℝ, ∀ y ∈ K, ‖iteratedFDeriv ℝ i f y‖ ≤ B := fun i hi =>
    hK.exists_bound_of_continuousOn
      ((ContinuousOn.continuousOn_iteratedFDeriv hf hs (by exact_mod_cast hi)).mono hKs)
  obtain ⟨B0, h0⟩ := h 0 (by norm_num)
  obtain ⟨B1, h1⟩ := h 1 (by norm_num)
  obtain ⟨B2, h2⟩ := h 2 le_rfl
  refine ⟨max B0 (max B1 B2), fun i hi y hy => ?_⟩
  interval_cases i
  · exact (h0 y hy).trans (le_max_left _ _)
  · exact (h1 y hy).trans ((le_max_left _ _).trans (le_max_right _ _))
  · exact (h2 y hy).trans ((le_max_right _ _).trans (le_max_right _ _))

end Calculus

theorem tendstoUniformlyOn_of_norm_le {Y α : Type*} [SeminormedAddCommGroup α] {F : ℝ → Y → α}
    {f : Y → α} {K : Set Y} {β : ℝ → ℝ} (hβ : Tendsto β (𝓝[>] 0) (𝓝 0))
    (h : ∀ᶠ t in 𝓝[>] 0, ∀ y ∈ K, ‖F t y - f y‖ ≤ β t) :
    TendstoUniformlyOn F f (𝓝[>] 0) K := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro e he
  filter_upwards [h, hβ.eventually (gt_mem_nhds he)] with t ht hβt y hy
  rw [dist_comm, dist_eq_norm]
  exact (ht y hy).trans_lt hβt

theorem tendsto_logErrorBound_nhdsWithin (C : ℝ) : Tendsto (fun t => errorWithLinear C t) (𝓝[>] 0) (𝓝 0) := by
  have hell : Tendsto ell (𝓝[>] (0 : ℝ)) atTop :=
    Real.tendsto_log_atTop.comp tendsto_inv_nhdsGT_zero
  have h1 : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have h2 : Tendsto (fun t => errE C t) (𝓝[>] 0) (𝓝 0) := by
    have := (h1.comp hell).const_mul C
    rw [mul_zero] at this
    refine this.congr fun t => ?_
    simp only [Function.comp, errE, mul_div_assoc]
  have h3 : Tendsto (fun t : ℝ => C * t) (𝓝[>] 0) (𝓝 0) := by
    have : Tendsto (fun t : ℝ => C * t) (𝓝 0) (𝓝 (C * 0)) :=
      (continuous_const.mul continuous_id).tendsto 0
    rw [mul_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  simpa [errorWithLinear] using h2.add h3

theorem logErrorBound_pos {C t : ℝ} (hC : 0 < C) (ht : 0 < t) (ht1 : t < Real.exp (-1)) :
    0 < errorWithLinear C t := by
  have hl : 1 < ell t := by
    have := Real.log_lt_log ht ht1
    rw [Real.log_exp] at this
    show 1 < Real.log t⁻¹
    rw [Real.log_inv]
    linarith
  have hlog : 0 < Real.log (ell t) := Real.log_pos hl
  have hl0 : 0 < ell t := by linarith
  unfold errorWithLinear errE
  positivity

end

end ArgumentConvergenceLemmas

end GroundTheory.Heights₂.Heights.AnalyticLimit
