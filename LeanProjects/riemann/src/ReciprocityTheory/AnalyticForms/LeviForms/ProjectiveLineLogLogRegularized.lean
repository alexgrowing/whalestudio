import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffFubiniStudyRatioCompChart0
import ReciprocityTheory.AnalyticForms.LeviForms.ProjLineChartTarget

namespace ReciprocityTheory.AnForm.P

open MeasureTheory ReciprocityTheory.AnForm.M FinHolAtlas Filter Topology
open scoped ContDiff

noncomputable section

def projectiveLineLogLog (y : OnePoint ℂ) : ℝ := -Real.log (rW fsPot projectiveLinePairSection y)

def projectiveLineLogLogRegularized (t : ℝ) (y : OnePoint ℂ) : ℝ :=
  if projectiveLinePairSection y y = 0 then -Real.log (Real.log (1 / t)) else
    ReciprocityTheory.AnForm.A.regMax (epsT 1 t) ![projectiveLineLogLog y, -Real.log (Real.log (1 / t))]

def ProjectiveLineLogLogInhabited : Prop :=
  (∀ y, logNormSec fsPot projectiveLinePairSection y ≤ 0) ∧ IsSingWeight p1 fsPot projectiveLinePairSection fsPot projectiveLineLogLog 1 ∧
    ∃ C t₀ : ℝ, IsRegFamily p1 fsPot fsPot projectiveLinePairSection fsPot projectiveLineLogLog projectiveLineLogLogRegularized C t₀ ∧
      IsRegFamilyC2 p1 projectiveLinePairSection projectiveLineLogLog projectiveLineLogLogRegularized

theorem projectiveLine_isRegFamily : IsRegFamily p1 fsPot fsPot projectiveLinePairSection fsPot llw llT 2 T0 := by
  refine ⟨Real.exp_pos _, (by rw [← Real.exp_zero]; exact Real.exp_lt_exp.2 (neg_lt_zero.2 (Real.exp_pos _))), fun t ht ht0 => ?_⟩
  have hη := eps_pos ht ht0
  have hL := logell_pos ht ht0
  have hℓ := ell_pos ht ht0
  have hr3 : 0 ≤ t ^ ((1 : ℝ) / 3) := Real.rpow_nonneg ht.le _
  refine ⟨llT_smooth t ht ht0, ?_, ?_, ?_, llT_psh t ht ht0, ?_, ?_, ?_⟩
  · intro y
    by_cases hy : y = OnePoint.infty
    · subst hy; rw [llT_infty]; linarith
    · rw [llT_ne t hy]
      have := rm_le (η := epsT 1 t) (a := llw y) (b := -Real.log (Real.log (1 / t))) (m := 0) hη.le
        (by linarith [projectiveLineLogLog_le_neg_one y]) (by linarith)
      linarith [eps_le_one ht ht0]
  · intro y hy
    rw [llT_ne t (fun h => hy ((mem_boundary_projectiveLine y).2 h))]
    exact rm_ge_left _ _ _
  · intro y
    by_cases hy : y = OnePoint.infty
    · subst hy; rw [llT_infty]; linarith
    · rw [llT_ne t hy]
      have := rm_ge_right (epsT 1 t) (llw y) (-Real.log (Real.log (1 / t)))
      linarith
  · intro y hy hr
    rw [llT_ne t (fun h => hy ((mem_boundary_projectiveLine y).2 h)), epsT_two]
    have hc : -Real.log (Real.log (1 / t)) ≤ llw y := by
      rw [llw]; exact neg_le_neg (Real.log_le_log (rW_pos y) hr)
    have := rm_le hη.le (le_refl (llw y)) hc
    linarith
  · intro y hy
    rw [llT_ne t (fun h => hy ((mem_boundary_projectiveLine y).2 h)), epsT_two]
    have hrp := rW_pos y
    have hre := projectiveLine_weight_ge_exp_one y
    have h1 : Real.log (rW fsPot projectiveLinePairSection y) - Real.log (Real.log (1 / t)) ≤
        rW fsPot projectiveLinePairSection y / Real.log (1 / t) := by
      rw [← Real.log_div hrp.ne' hℓ.ne']
      have := Real.log_le_sub_one_of_pos (div_pos hrp hℓ)
      linarith
    have h2 : rW fsPot projectiveLinePairSection y / Real.log (1 / t) ≤ epsT 1 t * rW fsPot projectiveLinePairSection y := by
      have e : epsT 1 t * rW fsPot projectiveLinePairSection y =
          Real.log (Real.log (1 / t)) * rW fsPot projectiveLinePairSection y / Real.log (1 / t) := by
        unfold epsT; ring
      rw [e]
      apply div_le_div_of_nonneg_right _ hℓ.le
      have := logell_big ht ht0
      nlinarith [one_le_exp_one]
    have hc : -Real.log (Real.log (1 / t)) ≤ llw y + epsT 1 t * rW fsPot projectiveLinePairSection y := by
      rw [llw]; linarith
    have hm : llw y ≤ llw y + epsT 1 t * rW fsPot projectiveLinePairSection y := by
      have := mul_nonneg hη.le hrp.le; linarith
    have := rm_le hη.le hm hc
    have h5 : epsT 1 t / 2 ≤ epsT 1 t * rW fsPot projectiveLinePairSection y := by nlinarith [one_le_exp_one]
    linarith
  · intro t' htt' ht0' y
    have ht' : 0 < t' := lt_of_lt_of_le ht htt'
    have hη' := eps_pos ht' ht0'
    have hmono := eps_mono ht htt' ht0'
    have hc : -Real.log (Real.log (1 / t)) ≤ -Real.log (Real.log (1 / t')) :=
      neg_le_neg (Real.log_le_log (ell_pos ht' ht0') (ell_anti ht htt'))
    rw [epsT_two]
    by_cases hy : y = OnePoint.infty
    · subst hy; rw [llT_infty, llT_infty]; linarith
    · rw [llT_ne t hy, llT_ne t' hy]
      have := rm_le (m := ReciprocityTheory.AnForm.A.regMax (epsT 1 t') ![llw y, -Real.log (Real.log (1 / t'))])
        hη.le (rm_ge_left _ _ _) (le_trans hc (rm_ge_right _ _ _))
      linarith

theorem tuo_of_eventually {α β : Type*} [UniformSpace β] {F : ℝ → α → β} {f : α → β}
    {p : Filter ℝ} {K : Set α} (h : ∀ᶠ t in p, ∀ y ∈ K, F t y = f y) :
    TendstoUniformlyOn F f p K := by
  intro u hu
  filter_upwards [h] with t ht y hy
  rw [ht y hy]
  exact refl_mem_uniformity hu

theorem regFamilyC2_of_chart (j : Fin 2) (K : Set (Fin 1 → ℂ))
    (hK : K ⊆ (p1.chart j).target ∩ (p1.chart j).symm ⁻¹' (bdry projectiveLinePairSection)ᶜ) (hKc : IsCompact K) :
    TendstoUniformlyOn (fun t => llT t ∘ (p1.chart j).symm) (llw ∘ (p1.chart j).symm)
        (nhdsWithin 0 (Set.Ioi 0)) K ∧
      TendstoUniformlyOn (fun t => fderiv ℝ (llT t ∘ (p1.chart j).symm))
        (fderiv ℝ (llw ∘ (p1.chart j).symm)) (nhdsWithin 0 (Set.Ioi 0)) K ∧
      TendstoUniformlyOn (fun t => fderiv ℝ (fderiv ℝ (llT t ∘ (p1.chart j).symm)))
        (fderiv ℝ (fderiv ℝ (llw ∘ (p1.chart j).symm))) (nhdsWithin 0 (Set.Ioi 0)) K := by
  have hVeq : (p1.chart j).target ∩ (p1.chart j).symm ⁻¹' (bdry projectiveLinePairSection)ᶜ =
      {w | j = 1 → w 0 ≠ 0} := Set.ext fun w => chartV_iff j w
  have hVo : IsOpen ((p1.chart j).target ∩ (p1.chart j).symm ⁻¹' (bdry projectiveLinePairSection)ᶜ) := by
    rw [hVeq]; exact isOpen_goodSet j
  obtain ⟨δ, hδ, hδV⟩ := hKc.exists_cthickening_subset_open hVo hK
  have hC : IsCompact (Metric.cthickening δ K) := hKc.cthickening
  have hgc : ContinuousOn (fun w => -Real.log (Real.exp 1 + 2 * fsGk j (fsQ w)))
      (Metric.cthickening δ K) :=
    (contDiffOn_llwChart j).continuousOn.mono (fun w hw => (chartV_iff j w).1 (hδV hw))
  obtain ⟨m, hm⟩ := hC.bddBelow_image hgc
  have hT : 0 < min T0 (Real.exp (-Real.exp (1 - m))) := lt_min (Real.exp_pos _) (Real.exp_pos _)
  have hev : ∀ᶠ t in nhdsWithin 0 (Set.Ioi 0), ∀ w ∈ Metric.cthickening δ K,
      llT t ((p1.chart j).symm w) = llw ((p1.chart j).symm w) := by
    filter_upwards [Ioo_mem_nhdsGT hT] with t ht
    intro w hw
    have ht0 : t ≤ T0 := le_trans ht.2.le (min_le_left _ _)
    have ht1 : t ≤ Real.exp (-Real.exp (1 - m)) := le_trans ht.2.le (min_le_right _ _)
    have hwj : j = 1 → w 0 ≠ 0 := (chartV_iff j w).1 (hδV hw)
    rw [llT_chart_eq t j w hwj, projectiveLineLogLog_chart j w hwj]
    apply rm_eq_left (eps_pos ht.1 ht0).le
    have h1 : Real.exp (1 - m) ≤ Real.log (1 / t) := ell_ge ht.1 ht1
    have h2 : 1 - m ≤ Real.log (Real.log (1 / t)) := by
      have := Real.log_le_log (Real.exp_pos _) h1
      rwa [Real.log_exp] at this
    have h3 := eps_le_one ht.1 ht0
    have h4 : m ≤ -Real.log (Real.exp 1 + 2 * fsGk j (fsQ w)) := hm ⟨w, hw, rfl⟩
    linarith
  have hloc : ∀ᶠ t in nhdsWithin 0 (Set.Ioi 0), ∀ y ∈ K,
      (llT t ∘ (p1.chart j).symm) =ᶠ[𝓝 y] (llw ∘ (p1.chart j).symm) := by
    filter_upwards [hev] with t ht y hy
    have hmem : Metric.thickening δ K ∈ 𝓝 y :=
      Metric.isOpen_thickening.mem_nhds (Metric.self_subset_thickening hδ K hy)
    filter_upwards [hmem] with w hw
    exact ht w (Metric.thickening_subset_cthickening δ K hw)
  refine ⟨tuo_of_eventually ?_, tuo_of_eventually ?_, tuo_of_eventually ?_⟩
  · filter_upwards [hloc] with t ht y hy
    exact (ht y hy).eq_of_nhds
  · filter_upwards [hloc] with t ht y hy
    exact (ht y hy).fderiv_eq (𝕜 := ℝ)
  · filter_upwards [hloc] with t ht y hy
    exact ((ht y hy).fderiv (𝕜 := ℝ)).fderiv_eq (𝕜 := ℝ)

theorem projectiveLine_isRegFamilyC2 : IsRegFamilyC2 p1 projectiveLinePairSection llw llT :=
  fun j K hK hKc => regFamilyC2_of_chart j K hK hKc

theorem isRegFamily_inhabited : IsRegFamilyInhabitStatement := by
  intro e X _ A Θ L s hΘ hpos hL
  have hT : (0 : ℝ) < Real.exp (-Real.exp 1) := Real.exp_pos _
  have hT1 : Real.exp (-Real.exp 1) < 1 := (by rw [← Real.exp_zero]; exact Real.exp_lt_exp.2 (neg_lt_zero.2 (Real.exp_pos _)))
  have hεnn : ∀ t, 0 < t → t ≤ Real.exp (-Real.exp 1) → 0 ≤ epsT 1 t := by
    intro t ht ht0
    have h1 : Real.exp 1 ≤ Real.log (1 / t) := ell_ge ht ht0
    have h2 : 0 ≤ Real.log (Real.log (1 / t)) :=
      Real.log_nonneg (by linarith [one_le_exp_one])
    unfold epsT
    rw [one_mul]
    exact div_nonneg h2 (by linarith [Real.exp_pos 1])
  have hlog : ∀ t, 0 < t → t ≤ Real.exp (-Real.exp 1) → 0 ≤ Real.log (Real.log (1 / t)) := by
    intro t ht ht0
    have h1 : Real.exp 1 ≤ Real.log (1 / t) := ell_ge ht ht0
    exact Real.log_nonneg (by linarith [one_le_exp_one])
  refine ⟨⟨hT, hT1, fun t ht ht0 => ?_⟩, fun j K _ _ => ⟨?_, ?_, ?_⟩⟩
  · have hε := hεnn t ht ht0
    have hr3 : 0 ≤ t ^ ((1 : ℝ) / 3) := Real.rpow_nonneg ht.le _
    refine ⟨fun j => contDiffOn_const, fun _ => zero_le_one, fun _ _ => le_refl _,
      fun _ => by linarith [hlog t ht ht0], ?_, fun _ _ _ => by linarith,
      fun y _ => ?_, fun t' htt' ht0' _ => ?_⟩
    · intro x j y hy w
      have hyD : y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' Θ.U x := ⟨hy.1, hy.2.2⟩
      have hc : ContDiffAt ℝ 2 (Θ.φ x ∘ (A.chart j).symm) y :=
        ((hΘ.1 x j).contDiffAt (((A.chart j).isOpen_inter_preimage_symm
          (Θ.isOpen_U x)).mem_nhds hyD)).of_le two_le_inf
      have h0 : 0 ≤ levi (Θ.φ x ∘ (A.chart j).symm) y w := by
        by_cases hw : w = 0
        · rw [hw, levi_zero]
        · exact (hpos x j y hyD w hw).le
      show 0 ≤ levi (fun z => Θ.φ x ((A.chart j).symm z) + 0 +
        epsT 1 t * Θ.φ x ((A.chart j).symm z)) y w
      simp only [add_zero]
      rw [levi_add_smul (f := fun z => Θ.φ x ((A.chart j).symm z))
        (g := fun z => Θ.φ x ((A.chart j).symm z)) (epsT 1 t) hc hc w]
      have := mul_nonneg hε h0
      exact add_nonneg h0 this
    · have h1 : Real.exp 1 ≤ rW L s y := by
        have := hL y; unfold rW; linarith
      have := mul_nonneg hε (le_trans (Real.exp_pos 1).le h1)
      linarith
    · have := hεnn t' (lt_of_lt_of_le ht htt') ht0'
      linarith
  · exact tuo_of_eventually (Eventually.of_forall fun _ _ _ => rfl)
  · exact tuo_of_eventually (Eventually.of_forall fun _ _ _ => rfl)
  · exact tuo_of_eventually (Eventually.of_forall fun _ _ _ => rfl)

theorem projectiveLineLogLog_inhabited : ProjectiveLineLogLogInhabited :=
  ⟨fun y => logNormSec_nonpos y, singWeight, 2, T0, projectiveLine_isRegFamily, projectiveLine_isRegFamilyC2⟩

theorem isRegFamilyInhabit : IsRegFamilyInhabitStatement := isRegFamily_inhabited

end

end ReciprocityTheory.AnForm.P
