import Mathlib
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StatementsPullback
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open Filter Topology Set ContinuousLinearMap
open scoped ContDiff
open ReciprocityTheory.AnForm.M (FinHolAtlas HoloMap)

noncomputable section

namespace C2ConvergencePullback

theorem tendstoUniformlyOn_bilin {α ι P Q R : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup Q] [NormedSpace ℝ Q] [NormedAddCommGroup R] [NormedSpace ℝ R]
    (β : P →L[ℝ] Q →L[ℝ] R) {F : ι → α → P} {G : α → P} {p : Filter ι} {S : Set α}
    (h : TendstoUniformlyOn F G p S) (b : α → Q) (M : ℝ) (hb : ∀ y ∈ S, ‖b y‖ ≤ M) :
    TendstoUniformlyOn (fun t y => β (F t y) (b y)) (fun y => β (G y) (b y)) p S := by
  rw [Metric.tendstoUniformlyOn_iff] at h ⊢
  intro ε hε
  have hβ : ‖β‖ + 1 ≠ 0 := by positivity
  have hM : |M| + 1 ≠ 0 := by positivity
  have hC : 0 < (‖β‖ + 1) * (|M| + 1) := by positivity
  filter_upwards [h (ε / ((‖β‖ + 1) * (|M| + 1))) (div_pos hε hC)] with t ht y hy
  have h1 := ht y hy
  rw [dist_eq_norm] at h1
  have hby : ‖b y‖ ≤ |M| + 1 := (hb y hy).trans ((le_abs_self M).trans (by linarith))
  have heq : β (G y) (b y) - β (F t y) (b y) = β (G y - F t y) (b y) := by
    rw [map_sub, sub_apply]
  rw [dist_eq_norm, heq]
  calc ‖β (G y - F t y) (b y)‖ ≤ ‖β‖ * ‖G y - F t y‖ * ‖b y‖ := β.le_opNorm₂ _ _
    _ ≤ (‖β‖ + 1) * ‖G y - F t y‖ * (|M| + 1) := by gcongr; linarith
    _ < (‖β‖ + 1) * (ε / ((‖β‖ + 1) * (|M| + 1))) * (|M| + 1) := by gcongr
    _ = ε := by field_simp

theorem tendstoUniformlyOn_bilin' {α ι P Q R : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup Q] [NormedSpace ℝ Q] [NormedAddCommGroup R] [NormedSpace ℝ R]
    (β : Q →L[ℝ] P →L[ℝ] R) {F : ι → α → P} {G : α → P} {p : Filter ι} {S : Set α}
    (h : TendstoUniformlyOn F G p S) (b : α → Q) (M : ℝ) (hb : ∀ y ∈ S, ‖b y‖ ≤ M) :
    TendstoUniformlyOn (fun t y => β (b y) (F t y)) (fun y => β (b y) (G y)) p S := by
  simpa only [flip_apply] using tendstoUniformlyOn_bilin β.flip h b M hb

theorem tendstoLocallyUniformlyOn_of_nhds {α β ι : Type*} [TopologicalSpace α] [UniformSpace β]
    {F : ι → α → β} {f : α → β} {p : Filter ι} {s : Set α}
    (h : ∀ x ∈ s, ∃ N ∈ 𝓝 x, TendstoUniformlyOn F f p N) : TendstoLocallyUniformlyOn F f p s := by
  intro u hu x hx
  obtain ⟨N, hN, hT⟩ := h x hx
  exact ⟨N, mem_nhdsWithin_of_mem_nhds hN, hT u hu⟩

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y]
  [NormedSpace ℝ Y]

theorem fderiv_fderiv_comp_eq {W : Set X} (hW : IsOpen W) {τ : X → Y}
    (hτ : ∀ y ∈ W, ContDiffAt ℝ 2 τ y) {U : Set Y} (hWU : MapsTo τ W U) {H : Y → ℝ}
    (hH : ∀ z ∈ U, ContDiffAt ℝ 2 H z) {Fh : X → ℝ} (hF : ∀ y ∈ W, Fh y = H (τ y)) {y : X}
    (hy : y ∈ W) :
    fderiv ℝ Fh y = (fderiv ℝ H (τ y)).comp (fderiv ℝ τ y) ∧
    fderiv ℝ (fderiv ℝ Fh) y =
      (compL ℝ X Y ℝ (fderiv ℝ H (τ y))).comp (fderiv ℝ (fderiv ℝ τ) y) +
        ((compL ℝ X Y ℝ).flip (fderiv ℝ τ y)).comp
          ((fderiv ℝ (fderiv ℝ H) (τ y)).comp (fderiv ℝ τ y)) := by
  have h1 : ∀ y' ∈ W, fderiv ℝ Fh y' = (fderiv ℝ H (τ y')).comp (fderiv ℝ τ y') := by
    intro y' hy'
    have heq : Fh =ᶠ[𝓝 y'] H ∘ τ := by
      filter_upwards [hW.mem_nhds hy'] with z hz using hF z hz
    rw [heq.fderiv_eq]
    exact fderiv_comp y' ((hH _ (hWU hy')).differentiableAt (by norm_num))
      ((hτ y' hy').differentiableAt (by norm_num))
  refine ⟨h1 y hy, ?_⟩
  have hev : fderiv ℝ Fh =ᶠ[𝓝 y] fun y' => (fderiv ℝ H (τ y')).comp (fderiv ℝ τ y') := by
    filter_upwards [hW.mem_nhds hy] with z hz using h1 z hz
  have hH' : HasFDerivAt (fderiv ℝ H) (fderiv ℝ (fderiv ℝ H) (τ y)) (τ y) :=
    (((hH _ (hWU hy)).fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num)).hasFDerivAt
  have hT : HasFDerivAt (fderiv ℝ τ) (fderiv ℝ (fderiv ℝ τ) y) y :=
    (((hτ y hy).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have hc : HasFDerivAt (fun y' => fderiv ℝ H (τ y'))
      ((fderiv ℝ (fderiv ℝ H) (τ y)).comp (fderiv ℝ τ y)) y :=
    hH'.comp y ((hτ y hy).differentiableAt (by norm_num)).hasFDerivAt
  rw [hev.fderiv_eq]
  exact (hc.clm_comp hT).fderiv

theorem local_c2_convergence_pullback {ι : Type*} {p : Filter ι} {W : Set X} (hW : IsOpen W) {τ : X → Y}
    (hτ : ∀ y ∈ W, ContDiffAt ℝ 2 τ y) {U : Set Y} (hWU : MapsTo τ W U)
    {G : ι → Y → ℝ} {Φ : Y → ℝ} (hG : ∀ᶠ t in p, ∀ z ∈ U, ContDiffAt ℝ 2 (G t) z)
    (hΦ : ∀ z ∈ U, ContDiffAt ℝ 2 Φ z) {F : ι → X → ℝ} {Ψ : X → ℝ}
    (hF : ∀ t, ∀ y ∈ W, F t y = G t (τ y)) (hΨ : ∀ y ∈ W, Ψ y = Φ (τ y))
    {K : Set X} (hK : IsCompact K) (hKW : K ⊆ W)
    (h0 : TendstoUniformlyOn G Φ p (τ '' K))
    (h1 : TendstoUniformlyOn (fun t => fderiv ℝ (G t)) (fderiv ℝ Φ) p (τ '' K))
    (h2 : TendstoUniformlyOn (fun t => fderiv ℝ (fderiv ℝ (G t))) (fderiv ℝ (fderiv ℝ Φ)) p
      (τ '' K)) :
    TendstoUniformlyOn F Ψ p K ∧ TendstoUniformlyOn (fun t => fderiv ℝ (F t)) (fderiv ℝ Ψ) p K ∧
      TendstoUniformlyOn (fun t => fderiv ℝ (fderiv ℝ (F t))) (fderiv ℝ (fderiv ℝ Ψ)) p K := by
  have hsub : K ⊆ τ ⁻¹' (τ '' K) := subset_preimage_image τ K
  have c0 := (h0.comp τ).mono hsub
  have c1 := (h1.comp τ).mono hsub
  have c2 := (h2.comp τ).mono hsub
  have hτc : ContDiffOn ℝ 2 τ W := fun y hy => (hτ y hy).contDiffWithinAt
  have hD1 : ContinuousOn (fderiv ℝ τ) W := hτc.continuousOn_fderiv_of_isOpen hW (by norm_num)
  have hD2 : ContinuousOn (fderiv ℝ (fderiv ℝ τ)) W :=
    (hτc.fderiv_of_isOpen hW (m := 1) (by norm_num)).continuousOn_fderiv_of_isOpen hW le_rfl
  obtain ⟨M1, hM1⟩ := hK.exists_bound_of_continuousOn (hD1.mono hKW)
  obtain ⟨M2, hM2⟩ := hK.exists_bound_of_continuousOn
    (f := fderiv ℝ (fderiv ℝ τ)) (by exact hD2.mono hKW)
  have hP : ∀ y ∈ K, ‖(compL ℝ X Y ℝ).flip (fderiv ℝ τ y)‖ ≤ ‖(compL ℝ X Y ℝ).flip‖ * M1 :=
    fun y hy => ((compL ℝ X Y ℝ).flip.le_opNorm _).trans
      (mul_le_mul_of_nonneg_left (hM1 y hy) (norm_nonneg _))
  refine ⟨?_, ?_, ?_⟩
  · refine (c0.congr ?_).congr_right ?_
    · exact Eventually.of_forall fun t y hy => (hF t y (hKW hy)).symm
    · exact fun y hy => (hΨ y (hKW hy)).symm
  · have hA := tendstoUniformlyOn_bilin (compL ℝ X Y ℝ) c1 (fderiv ℝ τ) M1 hM1
    refine (hA.congr ?_).congr_right ?_
    · filter_upwards [hG] with t ht y hy
      rw [(fderiv_fderiv_comp_eq hW hτ hWU ht (hF t) (hKW hy)).1]
      simp only [Function.comp_apply, compL_apply]
    · intro y hy
      rw [(fderiv_fderiv_comp_eq hW hτ hWU hΦ hΨ (hKW hy)).1]
      simp only [Function.comp_apply, compL_apply]
  · have hA := tendstoUniformlyOn_bilin (R := X →L[ℝ] X →L[ℝ] ℝ)
      (by exact (compL ℝ X (X →L[ℝ] Y) (X →L[ℝ] ℝ)).comp (compL ℝ X Y ℝ)) c1 (fderiv ℝ (fderiv ℝ τ)) M2 hM2
    have hI := tendstoUniformlyOn_bilin (P := Y →L[ℝ] Y →L[ℝ] ℝ) (Q := X →L[ℝ] Y)
      (R := X →L[ℝ] Y →L[ℝ] ℝ) (by exact compL ℝ X Y (Y →L[ℝ] ℝ)) (by exact c2) (fderiv ℝ τ) M1 hM1
    have hB := tendstoUniformlyOn_bilin' (P := X →L[ℝ] Y →L[ℝ] ℝ)
      (Q := (Y →L[ℝ] ℝ) →L[ℝ] (X →L[ℝ] ℝ)) (R := X →L[ℝ] X →L[ℝ] ℝ)
      (by exact compL ℝ X (Y →L[ℝ] ℝ) (X →L[ℝ] ℝ)) (by exact hI)
      (fun y => (compL ℝ X Y ℝ).flip (fderiv ℝ τ y)) _ (by exact hP)
    refine ((hA.add hB).congr ?_).congr_right ?_
    · filter_upwards [hG] with t ht y hy
      rw [(fderiv_fderiv_comp_eq hW hτ hWU ht (hF t) (hKW hy)).2]
      simp only [Pi.add_apply, Function.comp_apply, compL_apply, ContinuousLinearMap.comp_apply]
    · intro y hy
      rw [(fderiv_fderiv_comp_eq hW hτ hWU hΦ hΨ (hKW hy)).2]
      simp only [Pi.add_apply, Function.comp_apply, compL_apply, ContinuousLinearMap.comp_apply]

end C2ConvergencePullback

theorem C2ConvergencePullback.proof : C2ConvergencePullback.Statement := by
  intro D E Y Z _ _ B A f hf V hV g φ φ' hφ hφ' hg hconv j K hK hKs
  have hOo : IsOpen ((B.chart j).target ∩ (B.chart j).symm ⁻¹' (f ⁻¹' V)) :=
    (B.chart j).isOpen_inter_preimage_symm (hV.preimage hf.1)
  have h2 : (2 : WithTop ℕ∞) ≤ ∞ := by
    first | exact_mod_cast (le_top : (2 : ℕ∞) ≤ ⊤) | simp | exact WithTop.coe_le_coe.2 le_top
  have hloc : ∀ y0 ∈ (B.chart j).target ∩ (B.chart j).symm ⁻¹' (f ⁻¹' V), ∃ N ∈ 𝓝 y0,
      TendstoUniformlyOn (fun t y => (g t ∘ f) ((B.chart j).symm y))
        (fun y => φ' ((B.chart j).symm y)) (𝓝[>] 0) N ∧
      TendstoUniformlyOn (fun t y => fderiv ℝ (fun y' => (g t ∘ f) ((B.chart j).symm y')) y)
        (fun y => fderiv ℝ (fun y' => φ' ((B.chart j).symm y')) y) (𝓝[>] 0) N ∧
      TendstoUniformlyOn
        (fun t y => fderiv ℝ (fderiv ℝ fun y' => (g t ∘ f) ((B.chart j).symm y')) y)
        (fun y => fderiv ℝ (fderiv ℝ fun y' => φ' ((B.chart j).symm y')) y) (𝓝[>] 0) N := by
    intro y0 hy0
    obtain ⟨k, hk⟩ := A.cover (f ((B.chart j).symm y0))
    set W := (B.chart j).target ∩ (B.chart j).symm ⁻¹' (f ⁻¹' ((A.chart k).source ∩ V)) with hWdef
    have hWo : IsOpen W :=
      (B.chart j).isOpen_inter_preimage_symm (((A.chart k).open_source.inter hV).preimage hf.1)
    have hy0W : y0 ∈ W := ⟨hy0.1, hk, hy0.2⟩
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (hWo.mem_nhds hy0W)
    have hNW : Metric.closedBall y0 (ε / 2) ⊆ W :=
      (Metric.closedBall_subset_ball (half_lt_self hε)).trans hball
    set U := (A.chart k).target ∩ (A.chart k).symm ⁻¹' V with hUdef
    have hUo : IsOpen U := (A.chart k).isOpen_inter_preimage_symm hV
    set τ := A.chart k ∘ f ∘ (B.chart j).symm with hτdef
    have hτ : ∀ y ∈ W, ContDiffAt ℝ 2 τ y := by
      intro y hy
      have ha : AnalyticAt ℂ τ y := hf.2 j k y ⟨hy.1, hy.2.1⟩
      have hR : AnalyticAt ℝ τ y := ha.restrictScalars
      exact hR.contDiffAt
    have hWU : MapsTo τ W U := by
      intro y hy
      refine ⟨(A.chart k).map_source hy.2.1, ?_⟩
      show (A.chart k).symm ((A.chart k) (f ((B.chart j).symm y))) ∈ V
      rw [(A.chart k).left_inv hy.2.1]
      exact hy.2.2
    have hN : IsCompact (Metric.closedBall y0 (ε / 2)) := isCompact_closedBall _ _
    have hτN : IsCompact (τ '' Metric.closedBall y0 (ε / 2)) :=
      hN.image_of_continuousOn fun y hy => (hτ y (hNW hy)).continuousAt.continuousWithinAt
    obtain ⟨c0, c1, c2⟩ := hconv k _ hτN ((hWU.mono_left hNW).image_subset)
    refine ⟨Metric.closedBall y0 (ε / 2), Metric.closedBall_mem_nhds y0 (half_pos hε), ?_⟩
    refine C2ConvergencePullback.local_c2_convergence_pullback (G := fun t z => g t ((A.chart k).symm z))
      (Φ := fun z => φ ((A.chart k).symm z)) hWo hτ hWU ?_ ?_ ?_ ?_ hN hNW c0 c1 c2
    · filter_upwards [hg] with t ht z hz
      have hs := (show A.SmoothOn Set.univ (g t) from ht) k
      exact (hs.contDiffAt (((A.chart k).isOpen_inter_preimage_symm isOpen_univ).mem_nhds
        ⟨hz.1, trivial⟩)).of_le h2
    · intro z hz
      exact ((hφ k).contDiffAt (hUo.mem_nhds hz)).of_le h2
    · intro t y hy
      show g t (f ((B.chart j).symm y)) =
        g t ((A.chart k).symm ((A.chart k) (f ((B.chart j).symm y))))
      rw [(A.chart k).left_inv hy.2.1]
    · intro y hy
      show φ' ((B.chart j).symm y) = φ ((A.chart k).symm ((A.chart k) (f ((B.chart j).symm y))))
      rw [(A.chart k).left_inv hy.2.1]
      exact hφ' _ hy.2.2
  refine ⟨?_, ?_, ?_⟩
  · refine (tendstoLocallyUniformlyOn_iff_forall_isCompact hOo).1
      (C2ConvergencePullback.tendstoLocallyUniformlyOn_of_nhds fun y hy => ?_) K hKs hK
    obtain ⟨N, hN, h, -, -⟩ := hloc y hy
    exact ⟨N, hN, h⟩
  · refine (tendstoLocallyUniformlyOn_iff_forall_isCompact hOo).1
      (C2ConvergencePullback.tendstoLocallyUniformlyOn_of_nhds fun y hy => ?_) K hKs hK
    obtain ⟨N, hN, -, h, -⟩ := hloc y hy
    exact ⟨N, hN, h⟩
  · refine (tendstoLocallyUniformlyOn_iff_forall_isCompact hOo).1
      (C2ConvergencePullback.tendstoLocallyUniformlyOn_of_nhds fun y hy => ?_) K hKs hK
    obtain ⟨N, hN, -, -, h⟩ := hloc y hy
    exact ⟨N, hN, h⟩

end

end GroundTheory.Heights₂.Heights.AnalyticLimit
