import Mathlib
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.C2ConvergenceHypothesesNonempty
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open Filter Topology Metric
open ReciprocityTheory.AnForm.A (regMax Mollifier)
open ReciprocityTheory.AnForm.M (FinHolAtlas)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (RegChartData RegCharts errE errorWithLinear ell)

noncomputable section

theorem ell_tendsto_atTop : Tendsto ell (𝓝[>] 0) atTop :=
  Real.tendsto_log_atTop.comp tendsto_inv_nhdsGT_zero

theorem logErrorBound_tendsto_zero (C : ℝ) : Tendsto (errorWithLinear C) (𝓝[>] 0) (𝓝 0) := by
  have h1 : Tendsto (fun t => Real.log (ell t) ^ 1 / (1 * ell t + 0)) (𝓝[>] 0) (𝓝 0) :=
    (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp ell_tendsto_atTop
  have h2 : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
  have h := (h1.const_mul C).add (h2.const_mul C)
  simp only [mul_zero, add_zero, pow_one, one_mul] at h
  refine h.congr fun t => ?_
  simp only [errorWithLinear, errE]
  ring

theorem logErrorBound_eventually_pos (C : ℝ) (hC : 0 < C) :
    ∀ᶠ t in 𝓝[>] 0, 0 < t ∧ 0 < errorWithLinear C t ∧ C * t ≤ errorWithLinear C t := by
  filter_upwards [self_mem_nhdsWithin, ell_tendsto_atTop.eventually_gt_atTop 1] with t (ht : 0 < t) hl
  have hlog : 0 < Real.log (ell t) := Real.log_pos hl
  have h0 : 0 ≤ errE C t := div_nonneg (mul_nonneg hC.le hlog.le) (by linarith)
  have hCt : 0 < C * t := mul_pos hC ht
  refine ⟨ht, ?_, ?_⟩ <;> simp only [errorWithLinear] <;> linarith

section C2

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem tendstoUniformlyOn_finset_biUnion {α β ι κ : Type*} [UniformSpace β] {F : κ → α → β}
    {f : α → β} {p : Filter κ} (T : Finset ι) (S : ι → Set α)
    (h : ∀ i ∈ T, TendstoUniformlyOn F f p (S i)) : TendstoUniformlyOn F f p (⋃ i ∈ T, S i) := by
  intro u hu
  filter_upwards [(eventually_all_finset T).2 fun i hi => h i hi u hu] with n hn x hx
  obtain ⟨i, hi, hx⟩ := Set.mem_iUnion₂.1 hx
  exact hn i hi x hx

theorem TendstoC2On.sub_const {G : ℝ → E → ℝ} {f : E → ℝ} {K : Set E} {a : ℝ → ℝ}
    (h : TendstoC2On G f K) (ha : Tendsto a (𝓝[>] 0) (𝓝 0)) :
    TendstoC2On (fun t y => G t y - a t) f K := by
  have hd : ∀ t y, fderiv ℝ (fun y => G t y - a t) y = fderiv ℝ (G t) y :=
    fun t y => fderiv_sub_const (a t)
  have hd' : ∀ t, fderiv ℝ (fun y => G t y - a t) = fderiv ℝ (G t) := fun t => funext (hd t)
  refine ⟨Metric.tendstoUniformlyOn_iff.2 fun e he => ?_, by simpa only [hd'] using h.2.1,
    by simpa only [hd'] using h.2.2⟩
  filter_upwards [Metric.tendstoUniformlyOn_iff.1 h.1 (e / 2) (by positivity),
    Metric.tendsto_nhds.1 ha (e / 2) (by positivity)] with t h1 h2 y hy
  have h3 := h1 y hy
  rw [Real.dist_eq] at h3 h2 ⊢
  rw [sub_zero] at h2
  have h4 := abs_add_le (f y - G t y) (a t)
  rw [show f y - (G t y - a t) = f y - G t y + a t by ring]
  linarith

theorem TendstoC2On.congr_open {F G : ℝ → E → ℝ} {f : E → ℝ} {L U : Set E} (hU : IsOpen U)
    (hLU : L ⊆ U) (hFG : ∀ᶠ t in 𝓝[>] 0, ∀ y ∈ U, F t y = G t y) (h : TendstoC2On G f L) :
    TendstoC2On F f L := by
  have e0 : ∀ t, (∀ y ∈ U, F t y = G t y) → ∀ y ∈ U, F t =ᶠ[𝓝 y] G t :=
    fun t ht y hy => Filter.eventually_of_mem (hU.mem_nhds hy) ht
  refine ⟨h.1.congr ?_, h.2.1.congr ?_, h.2.2.congr ?_⟩
  · filter_upwards [hFG] with t ht y hy
    exact (ht y (hLU hy)).symm
  · filter_upwards [hFG] with t ht y hy
    exact (e0 t ht y (hLU hy)).fderiv_eq.symm
  · filter_upwards [hFG] with t ht y hy
    have h' : fderiv ℝ (F t) =ᶠ[𝓝 y] fderiv ℝ (G t) :=
      Filter.eventually_of_mem (hU.mem_nhds (hLU hy)) fun z hz => (e0 t ht z hz).fderiv_eq
    exact h'.fderiv_eq.symm

end C2

theorem PropertyF.proof (hL : GluedLocal.Statement) (hA : ArgumentConvergenceC2.Statement) : PropertyF.Statement := by
  intro X _ _ _ D A R ρ Cη η hη C hC hcmp k K hK hKs
  obtain ⟨t₀, ht₀, hcmp⟩ := hcmp
  have hloc : ∀ y₀ ∈ K, ∃ r > 0, TendstoC2On (fun t y => R.glued R.φ ρ η C t ((A.chart k).symm y))
      (fun y => R.φ ((A.chart k).symm y)) (closedBall y₀ r) := by
    intro y₀ hy₀
    obtain ⟨N, J, c, hNo, hx₀, hcJ, hJN, -, hglue⟩ := hL D A R ρ Cη η hη ((A.chart k).symm y₀)
    have hO : IsOpen ((A.chart k).target ∩ (A.chart k).symm ⁻¹' (R.Yo ∩ N)) :=
      (A.chart k).isOpen_inter_preimage_symm (R.isOpen_Yo.inter hNo)
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hO y₀ ⟨(hKs hy₀).1, (hKs hy₀).2, hx₀⟩
    have hLO : closedBall y₀ (r / 2) ⊆ (A.chart k).target ∩ (A.chart k).symm ⁻¹' (R.Yo ∩ N) :=
      (closedBall_subset_ball (by linarith)).trans hball
    refine ⟨r / 2, by positivity, ?_⟩
    let jj : Fin R.n → Fin R.n := fun j => if j ∈ J then j else c
    have hjj : ∀ j, jj j ∈ J := fun j => by
      by_cases h : j ∈ J
      · simp only [jj, h, if_true]
      · simp only [jj, h, if_false]; exact hcJ
    have hdata := fun j => hA D A R ρ Cη η hη C hC (jj j) k (closedBall y₀ (r / 2))
      (isCompact_closedBall _ _)
      (fun y hy => ⟨(hLO hy).1, (hLO hy).2.1, hJN _ (hjj j) (hLO hy).2.2⟩)
    choose Uj hUo hLU hfC hargC hT M hM using hdata
    let U := ((A.chart k).target ∩ (A.chart k).symm ⁻¹' N) ∩ ⋂ j, Uj j
    have hUo' : IsOpen U :=
      ((A.chart k).isOpen_inter_preimage_symm hNo).inter (isOpen_iInter_of_finite hUo)
    have hLU' : closedBall y₀ (r / 2) ⊆ U := fun y hy =>
      ⟨⟨(hLO hy).1, (hLO hy).2.2⟩, Set.mem_iInter.2 fun j => hLU j hy⟩
    have hUj : ∀ j, U ⊆ Uj j := fun j y hy => Set.mem_iInter.1 hy.2 j
    let u : ℝ → Fin R.n → (Fin D → ℂ) → ℝ := fun t j y =>
      if j ∈ J then R.regArg R.φ ρ η C t j ((A.chart k).symm y)
      else R.regArg R.φ ρ η C t c ((A.chart k).symm y) - errorWithLinear C t
    let a : Fin R.n → ℝ → ℝ := fun j t => if j ∈ J then 0 else errorWithLinear C t
    have ha : ∀ j, Tendsto (a j) (𝓝[>] 0) (𝓝 0) := fun j => by
      by_cases h : j ∈ J
      · simp only [a, h, if_true]; exact tendsto_const_nhds
      · simp only [a, h, if_false]; exact logErrorBound_tendsto_zero C
    have hu : ∀ t j, u t j = fun y => R.regArg R.φ ρ η C t (jj j) ((A.chart k).symm y) - a j t := by
      intro t j
      funext y
      by_cases h : j ∈ J
      · simp only [u, jj, a, h, if_true, sub_zero]
      · simp only [u, jj, a, h, if_false]
    have : Nonempty (Fin R.n) := ⟨c⟩
    let Mt : ℝ := ∑ j, |M j|
    have H := RegularizedMaxConvergenceC2.proof (Fin R.n) U (closedBall y₀ (r / 2)) (fun y => R.φ ((A.chart k).symm y)) u
      (errorWithLinear C) (fun t => Mt * (t + errorWithLinear C t)) hUo' hLU' ((hfC c).mono (hUj c)) ?ev
      (logErrorBound_tendsto_zero C) ?conv ?grad ?ratio
    · refine TendstoC2On.congr_open hUo' hLU' ?_ H
      filter_upwards [logErrorBound_eventually_pos C hC, nhdsWithin_le_nhds (Iio_mem_nhds ht₀),
        self_mem_nhdsWithin] with t ht (htt : t < t₀) (ht0 : 0 < t) y hy
      exact hglue C t ht.2.1 (hcmp t ht0 htt) _ hy.1.2
    case ev =>
      filter_upwards [logErrorBound_eventually_pos C hC, eventually_all.2 fun j => hargC j] with t ht hcd
      refine ⟨ht.2.1, fun j => ?_⟩
      rw [hu]
      exact ((hcd j).mono (hUj j)).sub contDiffOn_const
    case conv =>
      intro j
      have e : (fun t => u t j) =
          fun t y => R.regArg R.φ ρ η C t (jj j) ((A.chart k).symm y) - a j t := by
        funext t
        exact hu t j
      rw [e]
      exact (hT j).sub_const (ha j)
    case grad =>
      filter_upwards [logErrorBound_eventually_pos C hC, eventually_all.2 fun j => hM j] with t ht hMj j y hy
      rw [hu t j, fderiv_sub_const]
      have hnn : 0 ≤ t + errorWithLinear C t := by linarith [ht.1, ht.2.1]
      calc _ ≤ M j * (t + errorWithLinear C t) := hMj j y hy
        _ ≤ |M j| * (t + errorWithLinear C t) := mul_le_mul_of_nonneg_right (le_abs_self _) hnn
        _ ≤ Mt * (t + errorWithLinear C t) := mul_le_mul_of_nonneg_right
            (Finset.single_le_sum (f := fun i => |M i|) (fun i _ => abs_nonneg _)
              (Finset.mem_univ j)) hnn
    case ratio =>
      have hK0 : Tendsto (fun t => Mt ^ 2 * (1 / C + 1) ^ 2 * errorWithLinear C t) (𝓝[>] 0) (𝓝 0) := by
        simpa using (logErrorBound_tendsto_zero C).const_mul (Mt ^ 2 * (1 / C + 1) ^ 2)
      refine squeeze_zero' ?_ ?_ hK0
      · filter_upwards [logErrorBound_eventually_pos C hC] with t ht
        exact div_nonneg (sq_nonneg _) ht.2.1.le
      · filter_upwards [logErrorBound_eventually_pos C hC] with t ht
        obtain ⟨ht, hε, hCt⟩ := ht
        rw [div_le_iff₀ hε]
        have h1 : t ≤ 1 / C * errorWithLinear C t := by
          rw [one_div_mul_eq_div, le_div_iff₀ hC]
          linarith
        have h2 : 0 ≤ t + errorWithLinear C t := by linarith
        have h3 : t + errorWithLinear C t ≤ (1 / C + 1) * errorWithLinear C t := by linarith
        calc (Mt * (t + errorWithLinear C t)) ^ 2 = Mt ^ 2 * (t + errorWithLinear C t) ^ 2 := by ring
          _ ≤ Mt ^ 2 * ((1 / C + 1) * errorWithLinear C t) ^ 2 := by gcongr
          _ = Mt ^ 2 * (1 / C + 1) ^ 2 * errorWithLinear C t * errorWithLinear C t := by ring
  choose! r hr hTr using hloc
  obtain ⟨T, hTK, hcov⟩ := hK.elim_nhds_subcover (fun y => closedBall y (r y))
    fun y hy => closedBall_mem_nhds y (hr y hy)
  exact ⟨(tendstoUniformlyOn_finset_biUnion T _ fun y hy => (hTr y (hTK y hy)).1).mono hcov,
    (tendstoUniformlyOn_finset_biUnion T _ fun y hy => (hTr y (hTK y hy)).2.1).mono hcov,
    (tendstoUniformlyOn_finset_biUnion T _ fun y hy => (hTr y (hTK y hy)).2.2).mono hcov⟩

end

end GroundTheory.Heights₂.Heights.AnalyticLimit
