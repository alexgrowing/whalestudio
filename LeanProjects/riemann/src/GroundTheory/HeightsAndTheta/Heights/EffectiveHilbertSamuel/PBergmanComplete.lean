import Mathlib
import GroundTheory.HeightsAndTheta.Heights.EffectiveHilbertSamuel.StatementsBergmanComplete
import GroundTheory.HeightsAndTheta.Heights.EffectiveHilbertSamuel.StatementsTopDensityChart
import GroundTheory.HeightsAndTheta.Heights.EffectiveHilbertSamuel.StatementsLocUnifAnalytic
import GroundTheory.HeightsAndTheta.Heights.EffectiveHilbertSamuel.PExtension
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPolydiscSubmean
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.EffectiveHS

open MeasureTheory Set Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
  GroundTheory.Heights₂.Heights.HilbertSamuel
open scoped ENNReal

noncomputable section

namespace BergmanCompleteProof

variable {D : ℕ} {U : Type} [TopologicalSpace U]

theorem subMean {H : (Fin D → ℂ) → ℂ} {z : Fin D → ℂ} {R : ℝ} (hR : 0 < R)
    (hH : AnalyticOnNhd ℂ H (Metric.closedBall z R)) :
    ENNReal.ofReal (‖H z‖ ^ 2 * (Real.pi * R ^ 2) ^ D) ≤
      ∫⁻ y in Metric.closedBall z R, ENNReal.ofReal (‖H y‖ ^ 2) := by
  have hf : AnalyticOnNhd ℂ (fun w => H (w + z))
      (Metric.closedBall 0 (R / Real.sqrt ((1 : ℕ) : ℝ))) := by
    intro w hw
    have hw' : w + z ∈ Metric.closedBall z R := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hw
    have h2 : AnalyticAt ℂ (fun w : Fin D → ℂ => w + z) w := analyticAt_id.add analyticAt_const
    exact AnalyticAt.comp (g := H) (f := fun v : Fin D → ℂ => v + z) (x := w) (hH _ hw') h2
  have h := PolydiscSubmean.proof D 1 (fun _ => 0) R (fun w => H (w + z)) one_pos hR
    (fun _ => le_rfl) hf
  have hg : ∏ _j : Fin D, gaussDiscMass 0 R = (Real.pi * R ^ 2) ^ D := by
    simp [gaussDiscMass]
  simp only [Nat.cast_one, Real.sqrt_one, div_one, one_pow, inv_one, mul_one, zero_mul,
    Finset.sum_const_zero, mul_zero, Real.exp_zero, zero_add, hg] at h
  have htr : ∫ w in Metric.closedBall (0 : Fin D → ℂ) R, ‖H (w + z)‖ ^ 2 =
      ∫ y in Metric.closedBall z R, ‖H y‖ ^ 2 := by
    have e : (fun w : Fin D → ℂ => w + z) ⁻¹' Metric.closedBall z R =
        Metric.closedBall 0 R := by
      ext w; simp [dist_eq_norm]
    rw [← e]
    exact (measurePreserving_add_right volume z).setIntegral_preimage_emb
      (Homeomorph.addRight z).measurableEmbedding (fun y => ‖H y‖ ^ 2) _
  rw [htr] at h
  have hint : IntegrableOn (fun y => ‖H y‖ ^ 2) (Metric.closedBall z R) :=
    (hH.continuousOn.norm.pow 2).integrableOn_compact (isCompact_closedBall z R)
  calc ENNReal.ofReal (‖H z‖ ^ 2 * (Real.pi * R ^ 2) ^ D)
      ≤ ENNReal.ofReal (∫ y in Metric.closedBall z R, ‖H y‖ ^ 2) := ENNReal.ofReal_le_ofReal h
    _ = _ := ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun _ => by positivity)

theorem aem_dens (A : FinHolAtlas D U) (ψ : Fin A.n → U → ℝ)
    (hψc : ∀ k, ContinuousOn (ψ k ∘ (A.chart k).symm) (A.chart k).target) (k : Fin A.n)
    {u : U → ℂ} (hu : A.HoloOn (A.chart k).source u) :
    AEMeasurable (fun y => ENNReal.ofReal (2 ^ D * ‖u ((A.chart k).symm y)‖ ^ 2 *
      Real.exp (-ψ k ((A.chart k).symm y)))) (volume.restrict (piece A k)) := by
  refine ExtensionProof.aem_of_continuousOn A k ?_
  have h1 := ExtensionProof.continuousOn_of_holoOn A k hu
  exact ENNReal.continuous_ofReal.comp_continuousOn
    ((continuousOn_const.mul (h1.norm.pow 2)).mul (hψc k).neg.rexp)

theorem local_bound (hD : TopDensityChart.Statement) (A : FinHolAtlas D U)
    (L₂ L : HolLineBundle A) (m : ℕ) (ψ : Fin A.n → U → ℝ)
    (hψc : ∀ k, ContinuousOn (ψ k ∘ (A.chart k).symm) (A.chart k).target)
    (hψ : ∀ k l, ∀ x ∈ (A.chart k).source ∩ (A.chart l).source,
      ψ k x = ψ l x + Real.log (‖L₂.g k l x * L.g k l x ^ m‖ ^ 2))
    (c : Fin A.n) (y₀ : Fin D → ℂ) (hy₀ : y₀ ∈ (A.chart c).target) :
    ∃ R > 0, ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ H ∈ topSections A L₂ L m, ∀ z ∈ Metric.closedBall y₀ R,
      ENNReal.ofReal (‖H c ((A.chart c).symm z)‖ ^ 2) ≤ C * topNormSq A ψ H := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 (A.chart c).open_target y₀ hy₀
  set R := r / 3 with hRdef
  have hR : 0 < R := by positivity
  set K := Metric.closedBall y₀ (2 * R) with hKdef
  have hK : K ⊆ (A.chart c).target :=
    (Metric.closedBall_subset_ball (by rw [hRdef]; linarith)).trans hball
  obtain ⟨M, hM⟩ := (isCompact_closedBall y₀ (2 * R)).exists_bound_of_continuousOn
    ((hψc c).mono hK)
  set b : ℝ := (Real.pi * R ^ 2) ^ D with hbdef
  have hb : 0 < b := by positivity
  refine ⟨R, hR, ENNReal.ofReal (Real.exp M / 2 ^ D) * ENNReal.ofReal b⁻¹,
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top, fun H hH z hz => ?_⟩
  set h : (Fin D → ℂ) → ℂ := fun y => H c ((A.chart c).symm y) with hhdef
  have hzK : Metric.closedBall z R ⊆ K := by
    intro y hy
    rw [Metric.mem_closedBall] at hy hz ⊢
    linarith [dist_triangle y z y₀]
  have han : AnalyticOnNhd ℂ h (Metric.closedBall z R) := fun y hy =>
    hH.1 c c y ⟨hK (hzK hy), (A.chart c).map_target (hK (hzK hy))⟩
  have h1 := subMean hR han
  have h2 : ∫⁻ y in Metric.closedBall z R, ENNReal.ofReal (‖h y‖ ^ 2) ≤
      ∫⁻ y in K, ENNReal.ofReal (‖h y‖ ^ 2) := lintegral_mono_set hzK
  have h3 : ∫⁻ y in K, ENNReal.ofReal (‖h y‖ ^ 2) ≤
      ∫⁻ y in K, ENNReal.ofReal (Real.exp M / 2 ^ D) *
        ENNReal.ofReal (2 ^ D * ‖H c ((A.chart c).symm y)‖ ^ 2 *
          Real.exp (-ψ c ((A.chart c).symm y))) := by
    refine setLIntegral_mono' Metric.isClosed_closedBall.measurableSet fun y hy => ?_
    rw [← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hψy : ψ c ((A.chart c).symm y) ≤ M := (le_abs_self _).trans (hM y hy)
    have he : 1 ≤ Real.exp M * Real.exp (-ψ c ((A.chart c).symm y)) := by
      rw [← Real.exp_add]; exact Real.one_le_exp (by linarith)
    have h2D : (0 : ℝ) < 2 ^ D := by positivity
    have hs : 0 ≤ ‖h y‖ ^ 2 := by positivity
    calc ‖h y‖ ^ 2 ≤ ‖h y‖ ^ 2 * (Real.exp M * Real.exp (-ψ c ((A.chart c).symm y))) :=
          le_mul_of_one_le_right hs he
      _ = Real.exp M / 2 ^ D * (2 ^ D * ‖H c ((A.chart c).symm y)‖ ^ 2 *
            Real.exp (-ψ c ((A.chart c).symm y))) := by
          rw [hhdef]; field_simp
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top] at h3
  have h4 := hD D U A L₂ L m ψ H hψ hH.2.1 c K Metric.isClosed_closedBall.measurableSet hK
  have h5 : ENNReal.ofReal (‖h z‖ ^ 2 * b) ≤
      ENNReal.ofReal (Real.exp M / 2 ^ D) * topNormSq A ψ H :=
    h1.trans (h2.trans (h3.trans (mul_le_mul_right h4 _)))
  have h6 : ENNReal.ofReal (‖h z‖ ^ 2) = ENNReal.ofReal (‖h z‖ ^ 2 * b) * ENNReal.ofReal b⁻¹ := by
    rw [← ENNReal.ofReal_mul (by positivity), mul_assoc, mul_inv_cancel₀ hb.ne', mul_one]
  calc ENNReal.ofReal (‖H c ((A.chart c).symm z)‖ ^ 2) = ENNReal.ofReal (‖h z‖ ^ 2) := rfl
    _ ≤ ENNReal.ofReal (Real.exp M / 2 ^ D) * topNormSq A ψ H * ENNReal.ofReal b⁻¹ := by
        rw [h6]; exact mul_le_mul_left h5 _
    _ = _ := by ring

end BergmanCompleteProof

theorem BergmanComplete.proof (hD : TopDensityChart.Statement) (hW : LocUnifAnalytic.Statement) :
    BergmanComplete.Statement := by
  intro D U _ A L₂ L m ψ hψc hψ G hG hGf hGc
  classical

  have hcau : ∀ c, ∀ y₀ ∈ (A.chart c).target, ∃ R > 0,
      UniformCauchySeqOn (fun n y => G n c ((A.chart c).symm y)) atTop
        (Metric.closedBall y₀ R) := by
    intro c y₀ hy₀
    obtain ⟨R, hR, C, hC, hb⟩ :=
      BergmanCompleteProof.local_bound hD A L₂ L m ψ hψc hψ c y₀ hy₀
    refine ⟨R, hR, Metric.uniformCauchySeqOn_iff.2 fun ε hε => ?_⟩
    have ht : Tendsto (fun p : ℕ × ℕ => C * topNormSq A ψ (G p.1 - G p.2)) atTop (𝓝 0) := by
      simpa using ENNReal.Tendsto.const_mul hGc (Or.inr hC)
    have hε2 : (0 : ℝ) < ε ^ 2 := pow_pos hε 2
    obtain ⟨⟨N₁, N₂⟩, hN⟩ :=
      eventually_atTop.1 (ht.eventually (gt_mem_nhds (ENNReal.ofReal_pos.2 hε2)))
    refine ⟨max N₁ N₂, fun n hn p hp z hz => ?_⟩
    have h1 := (hb _ (sub_mem (hG n) (hG p)) z hz).trans_lt
      (hN (n, p) (Prod.mk_le_mk.2 ⟨le_of_max_le_left hn, le_of_max_le_right hp⟩))
    rw [ENNReal.ofReal_lt_ofReal_iff hε2] at h1
    rw [dist_eq_norm]
    exact lt_of_pow_lt_pow_left₀ 2 hε.le (by simpa using h1)

  let F : Fin A.n → U → ℂ := fun k x =>
    if x ∈ (A.chart k).source then limUnder atTop (fun n => G n k x) else 0
  have hlim : ∀ k x, Tendsto (fun n => G n k x) atTop (𝓝 (F k x)) := by
    intro k x
    by_cases hx : x ∈ (A.chart k).source
    · obtain ⟨R, hR, hU⟩ := hcau k (A.chart k x) ((A.chart k).map_source hx)
      have hcs := hU.cauchySeq (Metric.mem_closedBall_self hR.le)
      simp only [(A.chart k).left_inv hx] at hcs
      obtain ⟨a, ha⟩ := cauchySeq_tendsto_of_complete hcs
      simp only [F, if_pos hx]
      exact tendsto_nhds_limUnder ⟨a, ha⟩
    · have h0 : ∀ n, G n k x = 0 := fun n => (hG n).2.2 k x hx
      simp only [F, if_neg hx, h0]
      exact tendsto_const_nhds

  have hloc : ∀ k, TendstoLocallyUniformlyOn (fun n y => G n k ((A.chart k).symm y))
      (fun y => F k ((A.chart k).symm y)) atTop (A.chart k).target := by
    intro k u hu y₀ hy₀
    obtain ⟨R, hR, hU⟩ := hcau k y₀ hy₀
    have hT := hU.tendstoUniformlyOn_of_tendsto fun y _ => hlim k ((A.chart k).symm y)
    exact ⟨_, mem_nhdsWithin_of_mem_nhds (Metric.closedBall_mem_nhds y₀ hR), hT u hu⟩

  have hF : F ∈ topSections A L₂ L m := by
    refine ⟨fun k j => ?_, fun j k x hx => ?_, fun k x hx => ?_⟩
    · set V := (A.chart j).target ∩ (A.chart j).symm ⁻¹' (A.chart k).source
      have hV : IsOpen V := (A.chart j).continuousOn_symm.isOpen_inter_preimage
        (A.chart j).open_target (A.chart k).open_source
      have hmaps : MapsTo (fun y => A.chart k ((A.chart j).symm y)) V (A.chart k).target :=
        fun y hy => (A.chart k).map_source hy.2
      have hcont : ContinuousOn (fun y => A.chart k ((A.chart j).symm y)) V :=
        (A.chart k).continuousOn.comp ((A.chart j).continuousOn_symm.mono inter_subset_left)
          fun y hy => hy.2
      have h1 := (hloc k).comp _ hmaps hcont
      have h2 : TendstoLocallyUniformlyOn (fun n => G n k ∘ (A.chart j).symm)
          (F k ∘ (A.chart j).symm) atTop V := by
        refine (h1.congr fun n y hy => ?_).congr_right fun y hy => ?_
        · simp [(A.chart k).left_inv hy.2]
        · simp [(A.chart k).left_inv hy.2]
      exact hW D V _ _ hV (fun n => (hG n).1 k j) h2
    · have h1 : Tendsto (fun n => jac A j k x * L₂.g j k x * L.g j k x ^ m * G n k x) atTop
          (𝓝 (jac A j k x * L₂.g j k x * L.g j k x ^ m * F k x)) :=
        (hlim k x).const_mul _
      refine tendsto_nhds_unique (hlim j x) (h1.congr fun n => ?_)
      exact ((hG n).2.1 j k x hx).symm
    · simp [F, if_neg hx]

  have hconv : Tendsto (fun n => topNormSq A ψ (G n - F)) atTop (𝓝 0) := by
    rw [ENNReal.tendsto_nhds_zero]
    intro ε hε
    obtain ⟨⟨N₁, N₂⟩, hN⟩ := eventually_atTop.1 (hGc.eventually (gt_mem_nhds hε))
    rw [eventually_atTop]
    refine ⟨max N₁ N₂, fun n hn => ?_⟩
    refine ExtensionProof.chartIntegral_le_of_liminf A
      (fun p k x => ENNReal.ofReal (2 ^ D * ‖(G n - G (p + max N₁ N₂)) k x‖ ^ 2 *
        Real.exp (-ψ k x))) _ ε (fun p k => ?_) (fun p => ?_) (fun k x => ?_)
    · exact BergmanCompleteProof.aem_dens A ψ hψc k ((sub_mem (hG n) (hG _)).1 k)
    · exact (hN (n, p + max N₁ N₂) (Prod.mk_le_mk.2 ⟨le_of_max_le_left hn,
        (le_max_right N₁ N₂).trans (Nat.le_add_left _ _)⟩)).le
    · have ht : Tendsto (fun p => ENNReal.ofReal (2 ^ D * ‖(G n - G (p + max N₁ N₂)) k x‖ ^ 2 *
          Real.exp (-ψ k x))) atTop
          (𝓝 (ENNReal.ofReal (2 ^ D * ‖(G n - F) k x‖ ^ 2 * Real.exp (-ψ k x)))) := by
        have hp := (hlim k x).comp (tendsto_add_atTop_nat (max N₁ N₂))
        refine ENNReal.tendsto_ofReal (((((tendsto_const_nhds (x := G n k x)).sub hp).norm.pow
          2).const_mul _).mul_const _)
      exact ht.liminf_eq.ge
  refine ⟨F, hF, ?_, hconv⟩

  obtain ⟨n, hn⟩ := (hconv.eventually (gt_mem_nhds zero_lt_one)).exists
  have key : ∀ k x, ENNReal.ofReal (2 ^ D * ‖F k x‖ ^ 2 * Real.exp (-ψ k x)) ≤
      2 * ENNReal.ofReal (2 ^ D * ‖G n k x‖ ^ 2 * Real.exp (-ψ k x)) +
        2 * ENNReal.ofReal (2 ^ D * ‖(G n - F) k x‖ ^ 2 * Real.exp (-ψ k x)) := by
    intro k x
    have h1 : ‖F k x‖ ≤ ‖G n k x‖ + ‖(G n - F) k x‖ := by
      have e : F k x = G n k x - (G n - F) k x := by simp
      rw [e]; exact norm_sub_le _ _
    have h2 : ‖F k x‖ ^ 2 ≤ 2 * ‖G n k x‖ ^ 2 + 2 * ‖(G n - F) k x‖ ^ 2 := by
      nlinarith [norm_nonneg (F k x), norm_nonneg (G n k x), norm_nonneg ((G n - F) k x),
        sq_nonneg (‖G n k x‖ - ‖(G n - F) k x‖)]
    have hc : 0 ≤ 2 ^ D * Real.exp (-ψ k x) := by positivity
    rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num),
      ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have := mul_le_mul_of_nonneg_left h2 hc
    nlinarith
  have hsum := ExtensionProof.chartIntegral_mono A key
  rw [ExtensionProof.chartIntegral_add A _ _ fun k =>
      (BergmanCompleteProof.aem_dens A ψ hψc k ((hG n).1 k)).const_mul 2,
    ExtensionProof.chartIntegral_const_mul A 2 (by norm_num),
    ExtensionProof.chartIntegral_const_mul A 2 (by norm_num)] at hsum
  refine hsum.trans_lt (ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top (by norm_num) (hGf n),
    ENNReal.mul_lt_top (by norm_num) (hn.trans ENNReal.one_lt_top)⟩)

end

end GroundTheory.Heights₂.Heights.EffectiveHS
