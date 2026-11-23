import Mathlib
import ReciprocityTheory.AnalyticForms.LeviForms.RegGlue
import ReciprocityTheory.AnalyticForms.LeviForms.RegChartC
import ReciprocityTheory.AnalyticForms.LeviForms.TailCut
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.RegularizedMaxC2ExampleRealLine
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.TendstoLocallyUniformlyOnOfNhds
open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Ar.Giv.GlueC2

open GroundTheory.Heights₂.Heights.AnalyticLimit (TendstoC2On)

noncomputable section

section General

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem tendstoUniformlyOn_add_small {V α : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {N : Set α} {g₀ : ℝ → α → V} {g : α → V} {l : Filter ℝ} {s : ℝ → ℝ} {q : α → V} {C : ℝ}
    (hq : ∀ z ∈ N, ‖q z‖ ≤ C) (hs : Tendsto s l (𝓝 0)) (h : TendstoUniformlyOn g₀ g l N) :
    TendstoUniformlyOn (fun t z => g₀ t z + s t • q z) g l N := by
  rw [Metric.tendstoUniformlyOn_iff] at h ⊢
  intro ε hε
  have hC : 0 < |C| + 1 := by positivity
  have hs' : ∀ᶠ t in l, |s t| < ε / 2 / (|C| + 1) := by
    have := hs.eventually (Metric.ball_mem_nhds (0 : ℝ) (div_pos (half_pos hε) hC))
    filter_upwards [this] with t ht
    simpa [Real.dist_eq] using ht
  filter_upwards [h (ε / 2) (half_pos hε), hs'] with t h1 h2 z hz
  have h3 := h1 z hz
  have h4 : ‖s t • q z‖ < ε / 2 := by
    rw [norm_smul, Real.norm_eq_abs]
    have hqz : ‖q z‖ ≤ |C| + 1 := (hq z hz).trans ((le_abs_self C).trans (by linarith))
    calc |s t| * ‖q z‖ ≤ |s t| * (|C| + 1) := by gcongr
      _ < ε / 2 / (|C| + 1) * (|C| + 1) := by gcongr
      _ = ε / 2 := by field_simp
  calc dist (g z) (g₀ t z + s t • q z) ≤ dist (g z) (g₀ t z) + dist (g₀ t z) (g₀ t z + s t • q z) :=
        dist_triangle _ _ _
    _ = dist (g z) (g₀ t z) + ‖s t • q z‖ := by simp [dist_eq_norm]
    _ < ε := by linarith

theorem tendstoC2On_congr {U N : Set E} (hU : IsOpen U) (hN : N ⊆ U) {G G' : ℝ → E → ℝ} {p : E → ℝ}
    (h : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ z ∈ U, G' t z = G t z) (hc : TendstoC2On G' p N) :
    TendstoC2On G p N := by
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ z ∈ N, G' t =ᶠ[𝓝 z] G t := by
    filter_upwards [h] with t ht z hz
    filter_upwards [hU.mem_nhds (hN hz)] with y hy using ht y hy
  refine ⟨hc.1.congr ?_, hc.2.1.congr ?_, hc.2.2.congr ?_⟩
  · filter_upwards [hev] with t ht z hz using (ht z hz).eq_of_nhds
  · filter_upwards [hev] with t ht z hz using (ht z hz).fderiv_eq
  · filter_upwards [hev] with t ht z hz using (ht z hz).fderiv.fderiv_eq

theorem tendstoC2On_add_small {U N : Set E} (hU : IsOpen U) (hN : N ⊆ U) (hNc : IsCompact N)
    {a : ℝ → E → ℝ} {p Q : E → ℝ} {δ : ℝ → ℝ} (hδ : Tendsto δ (𝓝[>] 0) (𝓝 0))
    (hQ : ContDiffOn ℝ 2 Q U) (ha : ∀ᶠ t in 𝓝[>] (0 : ℝ), ContDiffOn ℝ 2 (a t) U)
    (h : TendstoC2On a p N) :
    TendstoC2On (fun t z => a t z + δ t * Q z) p N ∧
      ∃ C : ℝ, ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ z ∈ N,
        ‖fderiv ℝ (fun z => a t z + δ t * Q z) z - fderiv ℝ (a t) z‖ ≤ C * |δ t| := by
  have hD1 : ContinuousOn (fderiv ℝ Q) U := hQ.continuousOn_fderiv_of_isOpen hU (by norm_num)
  have hD2 : ContinuousOn (fderiv ℝ (fderiv ℝ Q)) U :=
    (hQ.fderiv_of_isOpen hU (m := 1) (by norm_num)).continuousOn_fderiv_of_isOpen hU le_rfl
  obtain ⟨M0, hM0⟩ := hNc.exists_bound_of_continuousOn (hQ.continuousOn.mono hN)
  obtain ⟨M1, hM1⟩ := hNc.exists_bound_of_continuousOn (hD1.mono hN)
  obtain ⟨M2, hM2⟩ := hNc.exists_bound_of_continuousOn
    (f := fderiv ℝ (fderiv ℝ Q)) (by exact hD2.mono hN)
  have hdiffQ : ∀ z ∈ U, DifferentiableAt ℝ Q z := fun z hz =>
    (hQ.contDiffAt (hU.mem_nhds hz)).differentiableAt (by norm_num)
  have hdiff2Q : ∀ z ∈ U, DifferentiableAt ℝ (fderiv ℝ Q) z := fun z hz =>
    ((hQ.contDiffAt (hU.mem_nhds hz)).fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num)
  have h1 : ∀ t, ContDiffOn ℝ 2 (a t) U → ∀ z ∈ U,
      fderiv ℝ (fun z => a t z + δ t * Q z) z = fderiv ℝ (a t) z + δ t • fderiv ℝ Q z := by
    intro t ht z hz
    have hd : DifferentiableAt ℝ (a t) z :=
      (ht.contDiffAt (hU.mem_nhds hz)).differentiableAt (by norm_num)
    have := (hd.hasFDerivAt.add ((hdiffQ z hz).hasFDerivAt.const_mul (δ t))).fderiv
    exact this
  have h2 : ∀ t, ContDiffOn ℝ 2 (a t) U → ∀ z ∈ U,
      fderiv ℝ (fderiv ℝ (fun z => a t z + δ t * Q z)) z =
        fderiv ℝ (fderiv ℝ (a t)) z + δ t • fderiv ℝ (fderiv ℝ Q) z := by
    intro t ht z hz
    have hev : fderiv ℝ (fun z => a t z + δ t * Q z) =ᶠ[𝓝 z]
        fun z => fderiv ℝ (a t) z + δ t • fderiv ℝ Q z := by
      filter_upwards [hU.mem_nhds hz] with y hy using h1 t ht y hy
    rw [hev.fderiv_eq]
    have hd : DifferentiableAt ℝ (fderiv ℝ (a t)) z :=
      ((ht.contDiffAt (hU.mem_nhds hz)).fderiv_right (m := 1) (by norm_num)).differentiableAt
        (by norm_num)
    exact (hd.hasFDerivAt.add ((hdiff2Q z hz).hasFDerivAt.const_smul (δ t))).fderiv
  refine ⟨⟨?_, ?_, ?_⟩, |M1|, ?_⟩
  · have := tendstoUniformlyOn_add_small (q := Q) hM0 hδ h.1
    simpa [smul_eq_mul] using this
  · have := tendstoUniformlyOn_add_small (q := fderiv ℝ Q) hM1 hδ h.2.1
    refine this.congr ?_
    filter_upwards [ha] with t ht z hz
    exact (h1 t ht z (hN hz)).symm
  · have := tendstoUniformlyOn_add_small (q := fderiv ℝ (fderiv ℝ Q)) hM2 hδ h.2.2
    refine this.congr ?_
    filter_upwards [ha] with t ht z hz
    exact (h2 t ht z (hN hz)).symm
  · filter_upwards [ha] with t ht z hz
    rw [h1 t ht z (hN hz), add_sub_cancel_left, norm_smul, Real.norm_eq_abs, mul_comm]
    exact mul_le_mul_of_nonneg_right ((hM1 z hz).trans (le_abs_self _)) (abs_nonneg _)

end General

section Chart

variable {e : ℕ} {X : Type} [TopologicalSpace X]

theorem chart_C2_convergence (A B : FinHolAtlas e X) (hAB : A.Compatible B) (jA : Fin A.n) (j : Fin B.n)
    (s : X → X → ℂ) (ph : X → ℝ) (hbd : IsClosed (bdry s)) (hph : A.SmoothOn (bdry s)ᶜ ph)
    {W' : Set X} (hW' : IsOpen W') (hWb : W' ⊆ chartBall B j (5 / 4)) (hWc : W' ⊆ (bdry s)ᶜ)
    (f : ℝ → X → ℝ) (hfs : ∀ᶠ t in 𝓝[>] (0 : ℝ), A.SmoothOn (chartBall B j (5 / 4)) (f t))
    (hconv : ∀ K' ⊆ ball (0 : Fin e → ℂ) (5 / 4) ∩ (B.chart j).symm ⁻¹' (bdry s)ᶜ, IsCompact K' →
      TendstoUniformlyOn (fun t => f t ∘ (B.chart j).symm) (ph ∘ (B.chart j).symm) (𝓝[>] 0) K' ∧
      TendstoUniformlyOn (fun t => fderiv ℝ (f t ∘ (B.chart j).symm))
        (fderiv ℝ (ph ∘ (B.chart j).symm)) (𝓝[>] 0) K' ∧
      TendstoUniformlyOn (fun t => fderiv ℝ (fderiv ℝ (f t ∘ (B.chart j).symm)))
        (fderiv ℝ (fderiv ℝ (ph ∘ (B.chart j).symm))) (𝓝[>] 0) K' ∧
      ∃ M : ℝ, ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ z ∈ K',
        ‖fderiv ℝ (f t ∘ (B.chart j).symm) z - fderiv ℝ (ph ∘ (B.chart j).symm) z‖ ≤ M * t)
    {N : Set (Fin e → ℂ)} (hNc : IsCompact N)
    (hN : N ⊆ (A.chart jA).target ∩ (A.chart jA).symm ⁻¹' W') :
    TendstoC2On (fun t => f t ∘ (A.chart jA).symm) (ph ∘ (A.chart jA).symm) N ∧
      ∃ M : ℝ, ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ z ∈ N,
        ‖fderiv ℝ (f t ∘ (A.chart jA).symm) z - fderiv ℝ (ph ∘ (A.chart jA).symm) z‖ ≤ M * t := by
  have h2 : (2 : WithTop ℕ∞) ≤ ∞ := by
    first | exact_mod_cast (le_top : (2 : ℕ∞) ≤ ⊤) | simp | exact WithTop.coe_le_coe.2 le_top
  set W := (A.chart jA).target ∩ (A.chart jA).symm ⁻¹' W' with hWdef
  have hWo : IsOpen W := (A.chart jA).isOpen_inter_preimage_symm hW'
  set U := ball (0 : Fin e → ℂ) (5 / 4) ∩
    ((B.chart j).target ∩ (B.chart j).symm ⁻¹' (bdry s)ᶜ) with hUdef
  have hUo : IsOpen U :=
    isOpen_ball.inter ((B.chart j).isOpen_inter_preimage_symm hbd.isOpen_compl)
  set τ := B.chart j ∘ (A.chart jA).symm with hτdef
  have hτ : ∀ y ∈ W, ContDiffAt ℝ 2 τ y := by
    intro y hy
    have ha : AnalyticAt ℂ τ y := hAB.1 jA j y ⟨hy.1, (hWb hy.2).1⟩
    have hR : AnalyticAt ℝ τ y := ha.restrictScalars
    exact hR.contDiffAt
  have hleft : ∀ y ∈ W, (B.chart j).symm (τ y) = (A.chart jA).symm y := fun y hy =>
    (B.chart j).left_inv (hWb hy.2).1
  have hWU : Set.MapsTo τ W U := by
    intro y hy
    refine ⟨(hWb hy.2).2, (B.chart j).map_source (hWb hy.2).1, ?_⟩
    show (B.chart j).symm (τ y) ∈ (bdry s)ᶜ
    rw [hleft y hy]
    exact hWc hy.2
  have hΦ : ∀ z ∈ U, ContDiffAt ℝ 2 (ph ∘ (B.chart j).symm) z := by
    intro z hz
    exact (((smoothOn_of_compatible hAB hbd.isOpen_compl hph) j).contDiffAt
      (((B.chart j).isOpen_inter_preimage_symm hbd.isOpen_compl).mem_nhds hz.2)).of_le h2
  have hG : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ z ∈ U, ContDiffAt ℝ 2 (f t ∘ (B.chart j).symm) z := by
    filter_upwards [hfs] with t ht z hz
    have hz' : z ∈ (B.chart j).target ∩ (B.chart j).symm ⁻¹' chartBall B j (5 / 4) := by
      refine ⟨hz.2.1, (B.chart j).map_target hz.2.1, ?_⟩
      show B.chart j ((B.chart j).symm z) ∈ ball (0 : Fin e → ℂ) (5 / 4)
      rw [(B.chart j).right_inv hz.2.1]
      exact hz.1
    exact (((smoothOn_of_compatible hAB (chartBall_isOpen B j _) ht) j).contDiffAt
      (((B.chart j).isOpen_inter_preimage_symm (chartBall_isOpen B j _)).mem_nhds hz')).of_le h2
  have hF : ∀ t, ∀ y ∈ W, (f t ∘ (A.chart jA).symm) y = (f t ∘ (B.chart j).symm) (τ y) := by
    intro t y hy
    simp only [Function.comp_apply]
    rw [hleft y hy]
  have hΨ : ∀ y ∈ W, (ph ∘ (A.chart jA).symm) y = (ph ∘ (B.chart j).symm) (τ y) := by
    intro y hy
    simp only [Function.comp_apply]
    rw [hleft y hy]
  have hτN : IsCompact (τ '' N) :=
    hNc.image_of_continuousOn fun y hy => (hτ y (hN hy)).continuousAt.continuousWithinAt
  have hτU : τ '' N ⊆ ball (0 : Fin e → ℂ) (5 / 4) ∩ (B.chart j).symm ⁻¹' (bdry s)ᶜ := by
    rintro _ ⟨y, hy, rfl⟩
    have := hWU (hN hy)
    exact ⟨this.1, this.2.2⟩
  obtain ⟨c0, c1, c2, M, hM⟩ := hconv _ hτU hτN
  refine ⟨GroundTheory.Heights₂.Heights.AnalyticLimit.C2ConvergencePullback.local_c2_convergence_pullback hWo hτ hWU hG hΦ hF hΨ hNc hN
    c0 c1 c2, ?_⟩
  have hτc : ContDiffOn ℝ 2 τ W := fun y hy => (hτ y hy).contDiffWithinAt
  have hD1 : ContinuousOn (fderiv ℝ τ) W := hτc.continuousOn_fderiv_of_isOpen hWo (by norm_num)
  obtain ⟨M1, hM1⟩ := hNc.exists_bound_of_continuousOn (hD1.mono hN)
  refine ⟨M * M1, ?_⟩
  filter_upwards [hM, hG] with t ht hGt z hz
  have e1 := (GroundTheory.Heights₂.Heights.AnalyticLimit.C2ConvergencePullback.fderiv_fderiv_comp_eq hWo hτ hWU hGt
    (hF t) (hN hz)).1
  have e2 := (GroundTheory.Heights₂.Heights.AnalyticLimit.C2ConvergencePullback.fderiv_fderiv_comp_eq hWo hτ hWU hΦ
    hΨ (hN hz)).1
  rw [e1, e2, ← ContinuousLinearMap.sub_comp]
  have h3 := ht (τ z) (Set.mem_image_of_mem τ hz)
  have h4 := hM1 z hz
  calc _ ≤ _ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ (M * t) * M1 := mul_le_mul h3 h4 (norm_nonneg _) ((norm_nonneg _).trans h3)
    _ = M * M1 * t := by ring

end Chart

end

end GlobalTheory.CompanionTheory.Ar.Giv.GlueC2

namespace GlobalTheory.CompanionTheory.Ar.Giv.GlueC2

noncomputable section

section Glue

variable {e : ℕ} {X : Type} [TopologicalSpace X]

lemma glue_local_unif [T2Space X] (B : FinHolAtlas e X)
    (h2 : ∀ j, closedBall (0 : Fin e → ℂ) 2 ⊆ (B.chart j).target)
    (y₀ : X) (k₀ : Fin B.n) (hk₀ : y₀ ∈ chartBall B k₀ 1) :
    ∃ W : Set X, IsOpen W ∧ y₀ ∈ W ∧ W ⊆ chartBall B k₀ 1 ∧
      (∀ j, y₀ ∈ chartBall B j (5 / 4) → W ⊆ chartBall B j (5 / 4)) ∧
      ∀ (f η : Fin B.n → X → ℝ) (δ Mb : ℝ), 0 ≤ δ → δ ≤ 1 →
        (∀ j, ∀ y ∈ chartBall B j 1, η j y = 0) → (∀ j, ∀ y ∉ chartBall B j (9 / 8), η j y = -1) →
        (∀ j, ∀ y ∈ chartBall B j (5 / 4), |f j y| ≤ Mb) →
        (∀ j k, ∀ y ∈ chartBall B j (5 / 4) ∩ chartBall B k (5 / 4), |f j y - f k y| ≤ δ) →
        ∀ j, y₀ ∉ chartBall B j (5 / 4) → ∀ y ∈ W,
          glueArg B f η δ Mb j y + δ ≤ glueArg B f η δ Mb k₀ y := by
  classical
  set Kc : Fin B.n → Set X := fun j => (B.chart j).symm '' closedBall (0 : Fin e → ℂ) (9 / 8)
  have hKsub : ∀ j, closedBall (0 : Fin e → ℂ) (9 / 8) ⊆ (B.chart j).target :=
    fun j => (closedBall_subset_closedBall (by norm_num)).trans (h2 j)
  have hKcl : ∀ j, IsClosed (Kc j) := fun j =>
    ((isCompact_closedBall _ _).image_of_continuousOn
      ((B.chart j).continuousOn_symm.mono (hKsub j))).isClosed
  have hKin : ∀ j, Kc j ⊆ chartBall B j (5 / 4) := by
    rintro j _ ⟨z, hz, rfl⟩
    refine ⟨(B.chart j).map_target (hKsub j hz), ?_⟩
    rw [Set.mem_preimage, (B.chart j).right_inv (hKsub j hz)]
    exact closedBall_subset_ball (by norm_num) hz
  have hnotK : ∀ j, ∀ y, y ∉ Kc j → y ∉ chartBall B j (9 / 8) := by
    intro j y hy hb
    exact hy ⟨B.chart j y, ball_subset_closedBall hb.2, (B.chart j).left_inv hb.1⟩
  let I : Finset (Fin B.n) := Finset.univ.filter fun j => y₀ ∈ chartBall B j (5 / 4)
  refine ⟨chartBall B k₀ 1 ∩ (⋂ j ∈ I, chartBall B j (5 / 4)) ∩ ⋂ j ∈ Iᶜ, (Kc j)ᶜ, ?_, ?_, ?_, ?_, ?_⟩
  · refine ((chartBall_isOpen B k₀ 1).inter ?_).inter ?_
    · exact isOpen_biInter_finset fun j _ => chartBall_isOpen B j _
    · exact isOpen_biInter_finset fun j _ => (hKcl j).isOpen_compl
  · refine ⟨⟨hk₀, ?_⟩, ?_⟩
    · simp only [Set.mem_iInter]; intro j hj; simpa [I] using hj
    · simp only [Set.mem_iInter]
      intro j hj hK
      have : y₀ ∈ chartBall B j (5 / 4) := hKin j hK
      simp [I, this] at hj
  · exact fun y hy => hy.1.1
  · intro j hj y hy
    have := hy.1.2
    simp only [Set.mem_iInter] at this
    exact this j (by simpa [I] using hj)
  · intro f η δ Mb hδ0 hδ1 hη0 hη1 hMb hov j hj y hy
    have hyK : y ∉ Kc j := by
      have := hy.2
      simp only [Set.mem_iInter] at this
      exact this j (by simpa [I] using hj)
    have hy0 : y ∈ chartBall B k₀ 1 := hy.1.1
    have hy5 : y ∈ chartBall B k₀ (5 / 4) := chartBall_mono B k₀ (by norm_num) hy0
    have hk : glueArg B f η δ Mb k₀ y = f k₀ y := by
      simp [glueArg, hy5, hη0 k₀ y hy0]
    rw [hk]
    unfold glueArg
    split_ifs with hj5
    · rw [hη1 j y (hnotK j y hyK)]
      have := hov j k₀ y ⟨hj5, hy5⟩
      have := (abs_le.1 this).2
      linarith [hδ0]
    · have := (abs_le.1 (hMb k₀ y hy5)).1
      linarith

lemma glue_loc_rep [T2Space X] (B : FinHolAtlas e X) [Nonempty (Fin B.n)]
    (h2 : ∀ j, closedBall (0 : Fin e → ℂ) 2 ⊆ (B.chart j).target)
    (y₀ : X) (k₀ : Fin B.n) (hk₀ : y₀ ∈ chartBall B k₀ 1) :
    ∃ (W : Set X) (I : Finset (Fin B.n)), IsOpen W ∧ y₀ ∈ W ∧ W ⊆ chartBall B k₀ 1 ∧ k₀ ∈ I ∧
      (∀ j ∈ I, W ⊆ chartBall B j (5 / 4)) ∧
      ∀ (f η : Fin B.n → X → ℝ) (δ Mb : ℝ), 0 < δ → δ ≤ 1 →
        (∀ j, ∀ y ∈ chartBall B j 1, η j y = 0) → (∀ j, ∀ y ∉ chartBall B j (9 / 8), η j y = -1) →
        (∀ j, ∀ y ∈ chartBall B j (5 / 4), |f j y| ≤ Mb) →
        (∀ j k, ∀ y ∈ chartBall B j (5 / 4) ∩ chartBall B k (5 / 4), |f j y - f k y| ≤ δ) →
        ∀ y ∈ W, ReciprocityTheory.AnForm.A.regMax δ (fun j => glueArg B f η δ Mb j y) =
          ReciprocityTheory.AnForm.A.regMax δ (fun j =>
            if j ∈ I then f j y + 4 * δ * η j y else f k₀ y + 4 * δ * η k₀ y - δ) := by
  classical
  obtain ⟨W, hWo, hyW, hWk, hWin, hWout⟩ := glue_local_unif B h2 y₀ k₀ hk₀
  let I : Finset (Fin B.n) := Finset.univ.filter fun j => y₀ ∈ chartBall B j (5 / 4)
  have hk₀I : k₀ ∈ I := by
    simp only [I, Finset.mem_filter, Finset.mem_univ, true_and]
    exact chartBall_mono B k₀ (by norm_num) hk₀
  refine ⟨W, I, hWo, hyW, hWk, hk₀I, fun j hj => hWin j (by simpa [I] using hj), ?_⟩
  intro f η δ Mb hδ hδ1 hη0 hη1 hMb hov y hy
  have hy5 : ∀ j ∈ I, y ∈ chartBall B j (5 / 4) := fun j hj => hWin j (by simpa [I] using hj) hy
  rw [regMax_dominated (Fin B.n) δ _ k₀ I hδ hk₀I (fun j hj =>
    hWout f η δ Mb hδ.le hδ1 hη0 hη1 hMb hov j (by simpa [I] using hj) y hy)]
  congr 1
  funext j
  have hk5 := hy5 k₀ hk₀I
  by_cases hj : j ∈ I
  · simp [hj, glueArg, hy5 j hj]
  · simp [hj, glueArg, hk5]

theorem reg_glue_explicit [CompactSpace X] [T2Space X] (A B : FinHolAtlas e X) [Nonempty (Fin B.n)]
    (Θ th : LocPot X) (hAB : A.Compatible B) (hcov : ∀ x, ∃ j, x ∈ chartBall B j 1)
    (h2 : ∀ j, closedBall (0 : Fin e → ℂ) 2 ⊆ (B.chart j).target)
    (hΘ : IsPotential A Θ) (hΘpos : IsPosPot A Θ) (hth : IsPotential A th)
    (η : Fin B.n → X → ℝ)
    (hη : ∀ j, A.Smooth (η j) ∧ (∀ y, -1 ≤ η j y ∧ η j y ≤ 0) ∧
      (∀ y ∈ chartBall B j 1, η j y = 0) ∧ ∀ y ∉ chartBall B j (9 / 8), η j y = -1) :
    ∃ K : ℝ, 0 < K ∧ ∀ (δ Mb : ℝ) (f : Fin B.n → X → ℝ), 0 < δ → δ ≤ 1 →
      (∀ j, A.SmoothOn (chartBall B j (5 / 4)) (f j)) →
      (∀ j, ∀ y ∈ chartBall B j (5 / 4), |f j y| ≤ Mb) →
      (∀ j, IsPshOn A (chartBall B j (5 / 4)) (th + LocPot.ofFun (f j))) →
      (∀ j k, ∀ y ∈ chartBall B j (5 / 4) ∩ chartBall B k (5 / 4), |f j y - f k y| ≤ δ) →
      A.Smooth (fun y => ReciprocityTheory.AnForm.A.regMax δ (fun j => glueArg B f η δ Mb j y)) ∧
      (∀ c₀ : ℝ, IsPsh A (th + LocPot.ofFun
        (fun y => ReciprocityTheory.AnForm.A.regMax δ (fun j => glueArg B f η δ Mb j y) + c₀) +
          Θ.rsmul (2 * K * δ))) ∧
      ∀ j, ∀ y ∈ chartBall B j (5 / 4),
        |ReciprocityTheory.AnForm.A.regMax δ (fun j => glueArg B f η δ Mb j y) - f j y| ≤ K * δ := by
  classical
  have hηs : ∀ j, A.Smooth (η j) := fun j => (hη j).1

  have hC : ∀ j, ∃ C : ℝ, IsPsh A (LocPot.ofFun (η j) + Θ.rsmul C) := fun j =>
    pshShift A Θ hΘ hΘpos (η j) (hηs j)
  choose Cj hCj using hC
  set K' : ℝ := ∑ j, |Cj j| with hK'
  have hK'ge : ∀ j, Cj j ≤ K' := fun j =>
    (le_abs_self _).trans (Finset.single_le_sum (f := fun j => |Cj j|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ j))
  have hK'0 : 0 ≤ K' := Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨4 * K' + 2, by linarith, ?_⟩
  intro δ Mb f hδ hδ1 hfs hMb hfp hov
  set F : X → ℝ := fun y => ReciprocityTheory.AnForm.A.regMax δ (fun j => glueArg B f η δ Mb j y) with hF

  have hRM := (ReciprocityTheory.AnForm.A.regMax_thm (Fin B.n)).1 δ hδ

  have hΘlevi : ∀ x jA, ∀ y ∈ (A.chart jA).target ∩ (A.chart jA).symm ⁻¹' Θ.U x, ∀ w : Fin e → ℂ,
      0 ≤ levi (Θ.φ x ∘ (A.chart jA).symm) y w := by
    intro x jA y hy w
    by_cases hw : w = 0
    · subst hw; simp [levi_zero]
    · exact (hΘpos x jA y hy w hw).le

  have hloc : ∀ y₀ : X, ∃ (W : Set X) (k₀ : Fin B.n) (I : Finset (Fin B.n)), IsOpen W ∧ y₀ ∈ W ∧
      W ⊆ chartBall B k₀ 1 ∧ k₀ ∈ I ∧ (∀ j ∈ I, W ⊆ chartBall B j (5 / 4)) ∧
      ∀ y ∈ W, F y = ReciprocityTheory.AnForm.A.regMax δ (fun j =>
        if j ∈ I then f j y + 4 * δ * η j y else f k₀ y + 4 * δ * η k₀ y - δ) := by
    intro y₀
    obtain ⟨k₀, hk₀⟩ := hcov y₀
    obtain ⟨W, I, hWo, hyW, hWk, hk₀I, hWI, hrep⟩ := glue_loc_rep B h2 y₀ k₀ hk₀
    exact ⟨W, k₀, I, hWo, hyW, hWk, hk₀I, hWI, fun y hy => hrep f η δ Mb hδ hδ1
      (fun j => (hη j).2.2.1) (fun j => (hη j).2.2.2) hMb hov y hy⟩

  have hbd : ∀ j, ∀ y ∈ chartBall B j (5 / 4), |F y - f j y| ≤ (4 * K' + 2) * δ := by
    intro j y hy
    have hup : ReciprocityTheory.AnForm.A.tmax (fun j' => glueArg B f η δ Mb j' y) ≤ f j y + δ := by
      apply ReciprocityTheory.AnForm.A.tmax_le
      intro j'
      unfold glueArg
      split_ifs with h'
      · have h1 := (abs_le.1 (hov j' j y ⟨h', hy⟩)).2
        have h2' : 4 * δ * η j' y ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (by linarith) ((hη j').2.1 y).2
        linarith
      · have := (abs_le.1 (hMb j y hy)).1
        linarith
    obtain ⟨k, hk⟩ := hcov y
    have hk5 : y ∈ chartBall B k (5 / 4) := chartBall_mono B k (by norm_num) hk
    have hlow : f j y - δ ≤ ReciprocityTheory.AnForm.A.tmax (fun j' => glueArg B f η δ Mb j' y) := by
      refine le_trans ?_ (ReciprocityTheory.AnForm.A.le_tmax _ k)
      have : glueArg B f η δ Mb k y = f k y := by
        simp [glueArg, hk5, (hη k).2.2.1 y hk]
      rw [this]
      have := (abs_le.1 (hov j k y ⟨hy, hk5⟩)).2
      linarith
    have h1 := (hRM.2.2.2.1 (fun j' => glueArg B f η δ Mb j' y)).1
    have h2' := (hRM.2.2.2.1 (fun j' => glueArg B f η δ Mb j' y)).2
    have hF' : F y = ReciprocityTheory.AnForm.A.regMax δ (fun j' => glueArg B f η δ Mb j' y) := rfl
    rw [abs_le]
    constructor <;> nlinarith

  have hsm : ∀ (jA : Fin A.n) (g : X → ℝ) (U : Set X), IsOpen U → A.SmoothOn U g →
      ∀ y ∈ (A.chart jA).target ∩ (A.chart jA).symm ⁻¹' U,
        ContDiffAt ℝ ∞ (g ∘ (A.chart jA).symm) y := fun jA g U hU hg y hy =>
    (hg jA).contDiffAt (((A.chart jA).isOpen_inter_preimage_symm hU).mem_nhds hy)
  have hsmη : ∀ (jA : Fin A.n) (j : Fin B.n), ∀ y ∈ (A.chart jA).target,
      ContDiffAt ℝ ∞ (η j ∘ (A.chart jA).symm) y := fun jA j y hy =>
    hsm jA (η j) Set.univ isOpen_univ (hηs j) y ⟨hy, trivial⟩
  refine ⟨?_, ?_, hbd⟩
  ·
    intro jA y' hy'
    have hyt : y' ∈ (A.chart jA).target := hy'.1
    obtain ⟨W, k₀, I, hWo, hyW, hWk, hk₀I, hWI, hWeq⟩ := hloc ((A.chart jA).symm y')
    have hV : (A.chart jA).target ∩ (A.chart jA).symm ⁻¹' W ∈ nhds y' :=

      ((A.chart jA).isOpen_inter_preimage_symm hWo).mem_nhds ⟨hyt, hyW⟩
    let G : (Fin e → ℂ) → (Fin B.n → ℝ) := fun z j =>
      if j ∈ I then f j ((A.chart jA).symm z) + 4 * δ * η j ((A.chart jA).symm z)
      else f k₀ ((A.chart jA).symm z) + 4 * δ * η k₀ ((A.chart jA).symm z) - δ
    have hG : ContDiffAt ℝ ∞ G y' := by
      refine contDiffAt_pi.2 fun j => ?_
      by_cases hj : j ∈ I
      · simp only [G, hj, if_true]
        exact (hsm jA (f j) _ (chartBall_isOpen B j _) (hfs j) y' ⟨hyt, hWI j hj hyW⟩).add
          (contDiffAt_const.mul (hsmη jA j y' hyt))
      · simp only [G, hj, if_false]
        exact ((hsm jA (f k₀) _ (chartBall_isOpen B k₀ _) (hfs k₀) y'
          ⟨hyt, hWI k₀ hk₀I hyW⟩).add (contDiffAt_const.mul (hsmη jA k₀ y' hyt))).sub
          contDiffAt_const
    have hcomp : ContDiffAt ℝ ∞ (ReciprocityTheory.AnForm.A.regMax δ ∘ G) y' := hRM.1.contDiffAt.comp y' hG
    refine (hcomp.congr_of_eventuallyEq ?_).contDiffWithinAt
    filter_upwards [hV] with z hz
    exact hWeq _ hz.2
  ·
    intro c₀ x jA y' hy' w
    have hyt : y' ∈ (A.chart jA).target := hy'.1
    have hyth : (A.chart jA).symm y' ∈ th.U x := hy'.2.1.1
    have hyΘ : (A.chart jA).symm y' ∈ Θ.U x := hy'.2.2
    obtain ⟨W, k₀, I, hWo, hyW, hWk, hk₀I, hWI, hWeq⟩ := hloc ((A.chart jA).symm y')
    set c : ℝ := 2 * (4 * K' + 2) * δ with hc
    set V := (A.chart jA).target ∩ (A.chart jA).symm ⁻¹' (W ∩ th.U x ∩ Θ.U x) with hVdef
    have hVo : IsOpen V :=
      (A.chart jA).isOpen_inter_preimage_symm ((hWo.inter (th.isOpen_U x)).inter (Θ.isOpen_U x))
    have hyV : y' ∈ V := ⟨hyt, ⟨hyW, hyth⟩, hyΘ⟩
    let P : Fin B.n → (Fin e → ℂ) → ℝ := fun j z =>
      th.φ x ((A.chart jA).symm z) + (if j ∈ I then f j ((A.chart jA).symm z)
        else f k₀ ((A.chart jA).symm z) - δ)
    let Q : Fin B.n → (Fin e → ℂ) → ℝ := fun j z =>
      if j ∈ I then η j ((A.chart jA).symm z) else η k₀ ((A.chart jA).symm z)
    let R : (Fin e → ℂ) → ℝ := fun z => Θ.φ x ((A.chart jA).symm z)
    let u : Fin B.n → (Fin e → ℂ) → ℝ := fun j z => ((P j z + 4 * δ * Q j z) + c * R z) + c₀

    have hPs : ∀ j, ∀ z ∈ V, ContDiffAt ℝ ∞ (P j) z := by
      intro j z hz
      have hzt : z ∈ (A.chart jA).target := hz.1
      have h1 : ContDiffAt ℝ ∞ (th.φ x ∘ (A.chart jA).symm) z :=
        contDiffAt_of_isPotential A th hth x jA ⟨hzt, hz.2.1.2⟩
      by_cases hj : j ∈ I
      · simp only [P, hj, if_true]
        exact h1.add (hsm jA (f j) _ (chartBall_isOpen B j _) (hfs j) z ⟨hzt, hWI j hj hz.2.1.1⟩)
      · simp only [P, hj, if_false]
        exact h1.add ((hsm jA (f k₀) _ (chartBall_isOpen B k₀ _) (hfs k₀) z
          ⟨hzt, hWI k₀ hk₀I hz.2.1.1⟩).sub contDiffAt_const)
    have hQs : ∀ j, ∀ z ∈ V, ContDiffAt ℝ ∞ (Q j) z := by
      intro j z hz
      by_cases hj : j ∈ I
      · simp only [Q, hj, if_true]; exact hsmη jA j z hz.1
      · simp only [Q, hj, if_false]; exact hsmη jA k₀ z hz.1
    have hRs : ∀ z ∈ V, ContDiffAt ℝ ∞ R z := fun z hz =>
      contDiffAt_of_isPotential A Θ hΘ x jA ⟨hz.1, hz.2.2⟩
    have hus : ∀ j, ContDiffOn ℝ 2 (u j) V := by
      intro j z hz
      exact (((((hPs j z hz).add (contDiffAt_const.mul (hQs j z hz))).add
        (contDiffAt_const.mul (hRs z hz))).add contDiffAt_const).of_le (by norm_cast)).contDiffWithinAt

    have heq : ((th + LocPot.ofFun (fun y => F y + c₀) + Θ.rsmul c).φ x ∘ (A.chart jA).symm) =ᶠ[nhds y']
        (fun z => ReciprocityTheory.AnForm.A.regMax δ (fun j => u j z)) := by
      filter_upwards [hVo.mem_nhds hyV] with z hz
      have hF' := hWeq _ hz.2.1.1
      show th.φ x ((A.chart jA).symm z) + (F ((A.chart jA).symm z) + c₀) +
          c * Θ.φ x ((A.chart jA).symm z) = _
      rw [hF']
      set C0 : ℝ := th.φ x ((A.chart jA).symm z) + c * Θ.φ x ((A.chart jA).symm z) + c₀ with hC0
      have htr := hRM.2.2.2.2.2.2.1 (fun j => if j ∈ I then f j ((A.chart jA).symm z) +
          4 * δ * η j ((A.chart jA).symm z) else f k₀ ((A.chart jA).symm z) +
          4 * δ * η k₀ ((A.chart jA).symm z) - δ) C0
      have hu : (fun j => u j z) = (fun j => (if j ∈ I then f j ((A.chart jA).symm z) +
          4 * δ * η j ((A.chart jA).symm z) else f k₀ ((A.chart jA).symm z) +
          4 * δ * η k₀ ((A.chart jA).symm z) - δ) + C0) := by
        funext j
        by_cases hj : j ∈ I
        · simp only [u, P, Q, R, hj, if_true, hC0]; ring
        · simp only [u, P, Q, R, hj, if_false, hC0]; ring
      rw [hu, htr, hC0]
      ring
    rw [levi_congr heq w]
    refine ReciprocityTheory.AnForm.A.regMaxLevi_thm e (Fin B.n) δ V u hVo hδ hus y' hyV w 0 ?_
    intro j

    have hP2 := (hPs j y' hyV).of_le (show (2 : WithTop ℕ∞) ≤ ∞ by norm_cast)
    have hQ2 := (hQs j y' hyV).of_le (show (2 : WithTop ℕ∞) ≤ ∞ by norm_cast)
    have hR2 := (hRs y' hyV).of_le (show (2 : WithTop ℕ∞) ≤ ∞ by norm_cast)
    have hl1 : levi (u j) y' w = levi (P j) y' w + 4 * δ * levi (Q j) y' w + c * levi R y' w := by
      have e1 : levi (fun z => P j z + 4 * δ * Q j z) y' w =
          levi (P j) y' w + 4 * δ * levi (Q j) y' w := levi_add_smul (4 * δ) hP2 hQ2 w
      have e2 : levi (fun z => (P j z + 4 * δ * Q j z) + c * R z) y' w =
          levi (fun z => P j z + 4 * δ * Q j z) y' w + c * levi R y' w :=
        levi_add_smul c (hP2.add (contDiffAt_const.mul hQ2)) hR2 w
      have e3 : levi (fun z => ((P j z + 4 * δ * Q j z) + c * R z) +
            c₀ * (fun _ : Fin e → ℂ => (1 : ℝ)) z) y' w =
          levi (fun z => (P j z + 4 * δ * Q j z) + c * R z) y' w +
            c₀ * levi (fun _ : Fin e → ℂ => (1 : ℝ)) y' w :=
        levi_add_smul c₀ ((hP2.add (contDiffAt_const.mul hQ2)).add (contDiffAt_const.mul hR2))
          contDiffAt_const w
      have h00 : levi (fun _ : Fin e → ℂ => (1 : ℝ)) y' w = 0 := by simp [levi]
      have hue : u j = fun z => ((P j z + 4 * δ * Q j z) + c * R z) +
          c₀ * (fun _ : Fin e → ℂ => (1 : ℝ)) z := by
        funext z; simp [u]
      rw [hue, e3, e2, e1, h00]; ring
    have hRl : 0 ≤ levi R y' w := hΘlevi x jA y' ⟨hyt, hyΘ⟩ w

    have hPl : 0 ≤ levi (P j) y' w := by
      by_cases hj : j ∈ I
      · have := hfp j x jA y' ⟨hyt, ⟨hyth, trivial⟩, hWI j hj hyW⟩ w
        have hPe : P j = (th + LocPot.ofFun (f j)).φ x ∘ (A.chart jA).symm := by
          funext z; simp only [P, hj, if_true]; rfl
        rw [hPe]; exact this
      · have := hfp k₀ x jA y' ⟨hyt, ⟨hyth, trivial⟩, hWI k₀ hk₀I hyW⟩ w
        have hg2 : ContDiffAt ℝ 2 ((th + LocPot.ofFun (f k₀)).φ x ∘ (A.chart jA).symm) y' := by
          have h1 : ContDiffAt ℝ ∞ (th.φ x ∘ (A.chart jA).symm) y' :=
            contDiffAt_of_isPotential A th hth x jA ⟨hyt, hyth⟩
          exact (h1.add (hsm jA (f k₀) _ (chartBall_isOpen B k₀ _) (hfs k₀) y'
            ⟨hyt, hWI k₀ hk₀I hyW⟩)).of_le (by norm_cast)
        have hPe : P j = fun z => ((th + LocPot.ofFun (f k₀)).φ x ∘ (A.chart jA).symm) z +
            (-δ) * (fun _ => (1 : ℝ)) z := by
          funext z; simp only [P, hj, if_false]; show _ = th.φ x _ + f k₀ _ + _; ring
        rw [hPe, levi_add_smul (-δ) hg2 contDiffAt_const w]
        have h0 : levi (fun _ : Fin e → ℂ => (1 : ℝ)) y' w = 0 := by simp [levi]
        rw [h0]; linarith

    have hQl : 0 ≤ levi (Q j) y' w + K' * levi R y' w := by
      have key : ∀ j', Q j = η j' ∘ (A.chart jA).symm → 0 ≤ levi (Q j) y' w + K' * levi R y' w := by
        intro j' hQe
        have h0 := hCj j' x jA y' ⟨hyt, ⟨trivial, hyΘ⟩⟩ w
        have hQR : (LocPot.ofFun (η j') + Θ.rsmul (Cj j')).φ x ∘ (A.chart jA).symm =
            fun z => (η j' ∘ (A.chart jA).symm) z + Cj j' * R z := rfl
        rw [hQR, levi_add_smul (Cj j') (hsmη jA j' y' hyt |>.of_le (by norm_cast)) hR2 w] at h0
        rw [hQe]
        nlinarith [hK'ge j']
      by_cases hj : j ∈ I
      · exact key j (by funext z; simp [Q, hj])
      · exact key k₀ (by funext z; simp [Q, hj])
    rw [hl1]
    have : 0 ≤ 4 * δ * (levi (Q j) y' w + K' * levi R y' w) := by positivity
    have h2δ : 0 ≤ (4 * K' + 4) * δ * levi R y' w :=
      mul_nonneg (mul_nonneg (by linarith) hδ.le) hRl
    have hcv : c = 2 * (4 * K' + 2) * δ := hc
    rw [hcv]
    nlinarith

end Glue

end

end GlobalTheory.CompanionTheory.Ar.Giv.GlueC2

namespace GlobalTheory.CompanionTheory.Ar.Giv.GlueC2

open GroundTheory.Heights₂.Heights.AnalyticLimit (TendstoC2On)

noncomputable section

variable {e : ℕ} {X : Type} [TopologicalSpace X]

theorem glue_C2_local [T2Space X] (A B : FinHolAtlas e X) [Nonempty (Fin B.n)] (s : X → X → ℂ)
    (ph : X → ℝ) (hAB : A.Compatible B) (hcov : ∀ x, ∃ j, x ∈ chartBall B j 1)
    (h2 : ∀ j, closedBall (0 : Fin e → ℂ) 2 ⊆ (B.chart j).target)
    (hbd : IsClosed (bdry s)) (hph : A.SmoothOn (bdry s)ᶜ ph) (η : Fin B.n → X → ℝ)
    (hη : ∀ j, A.Smooth (η j) ∧ (∀ y, -1 ≤ η j y ∧ η j y ≤ 0) ∧
      (∀ y ∈ chartBall B j 1, η j y = 0) ∧ ∀ y ∉ chartBall B j (9 / 8), η j y = -1)
    (K₀ t₀ : ℝ) (δ Mb : ℝ → ℝ) (f : ℝ → Fin B.n → X → ℝ) (ht₀ : 0 < t₀)
    (hδ : Tendsto δ (𝓝[>] 0) (𝓝 0))
    (H : ∀ t, 0 < t → t ≤ t₀ → t ≤ δ t ∧ δ t ≤ 1 ∧
      (∀ j, A.SmoothOn (chartBall B j (5 / 4)) (f t j)) ∧
      (∀ j, ∀ y ∈ chartBall B j (5 / 4), |f t j y| ≤ Mb t) ∧
      ∀ j k, ∀ y ∈ chartBall B j (5 / 4) ∩ chartBall B k (5 / 4), |f t j y - f t k y| ≤ δ t)
    (hc : ∀ j, ∀ K' ⊆ ball (0 : Fin e → ℂ) (5 / 4) ∩ (B.chart j).symm ⁻¹' (bdry s)ᶜ, IsCompact K' →
      TendstoUniformlyOn (fun t => f t j ∘ (B.chart j).symm) (ph ∘ (B.chart j).symm) (𝓝[>] 0) K' ∧
      TendstoUniformlyOn (fun t => fderiv ℝ (f t j ∘ (B.chart j).symm))
        (fderiv ℝ (ph ∘ (B.chart j).symm)) (𝓝[>] 0) K' ∧
      TendstoUniformlyOn (fun t => fderiv ℝ (fderiv ℝ (f t j ∘ (B.chart j).symm)))
        (fderiv ℝ (fderiv ℝ (ph ∘ (B.chart j).symm))) (𝓝[>] 0) K' ∧
      ∃ M : ℝ, ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ z ∈ K',
        ‖fderiv ℝ (f t j ∘ (B.chart j).symm) z - fderiv ℝ (ph ∘ (B.chart j).symm) z‖ ≤ M * t)
    (jA : Fin A.n) (z₀ : Fin e → ℂ)
    (hz₀ : z₀ ∈ (A.chart jA).target ∩ (A.chart jA).symm ⁻¹' (bdry s)ᶜ) :
    ∃ N ∈ 𝓝 z₀, TendstoC2On (fun t => (fun y => ReciprocityTheory.AnForm.A.regMax (δ t)
        (fun j => glueArg B (f t) η (δ t) (Mb t) j y) + K₀ * δ t) ∘ (A.chart jA).symm)
      (ph ∘ (A.chart jA).symm) N := by
  classical
  have ev : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t ∧ t ≤ t₀ := by
    filter_upwards [Ioc_mem_nhdsGT ht₀] with t ht using ht
  have h2' : (2 : WithTop ℕ∞) ≤ ∞ := by
    first | exact_mod_cast (le_top : (2 : ℕ∞) ≤ ⊤) | simp | exact WithTop.coe_le_coe.2 le_top
  obtain ⟨k₀, hk₀⟩ := hcov ((A.chart jA).symm z₀)
  obtain ⟨W, I, hWo, hyW, hWk, hk₀I, hWI, hrep⟩ := glue_loc_rep B h2 _ k₀ hk₀
  set W' := W ∩ (bdry s)ᶜ with hW'def
  have hW'o : IsOpen W' := hWo.inter hbd.isOpen_compl
  set U := (A.chart jA).target ∩ (A.chart jA).symm ⁻¹' W' with hUdef
  have hUo : IsOpen U := (A.chart jA).isOpen_inter_preimage_symm hW'o
  have hzU : z₀ ∈ U := ⟨hz₀.1, hyW, hz₀.2⟩
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 (hUo.mem_nhds hzU)
  set N := closedBall z₀ (r / 2) with hNdef
  have hNU : N ⊆ U := (closedBall_subset_ball (half_lt_self hr)).trans hball
  have hNc : IsCompact N := isCompact_closedBall _ _
  refine ⟨N, closedBall_mem_nhds z₀ (half_pos hr), ?_⟩
  set p := ph ∘ (A.chart jA).symm with hp
  have hpC : ContDiffOn ℝ 2 p U :=
    ((hph jA).of_le h2').mono fun z hz => ⟨hz.1, hz.2.2⟩
  let b : Fin B.n → Fin B.n := fun j => if j ∈ I then j else k₀
  have hb : ∀ j, b j ∈ I := by
    intro j
    by_cases hj : j ∈ I
    · simpa [b, hj] using hj
    · simpa [b, hj] using hk₀I
  have hWb : ∀ j, W' ⊆ chartBall B (b j) (5 / 4) := fun j y hy => hWI _ (hb j) hy.1
  let Q : Fin B.n → (Fin e → ℂ) → ℝ := fun j z =>
    4 * η (b j) ((A.chart jA).symm z) - (if j ∈ I then 0 else 1)
  have hQ : ∀ j, ContDiffOn ℝ 2 (Q j) U := by
    intro j
    have h1 : ContDiffOn ℝ 2 (η (b j) ∘ (A.chart jA).symm) U :=
      (((hη (b j)).1 jA).of_le h2').mono fun z hz => ⟨hz.1, trivial⟩
    exact (contDiffOn_const.mul h1).sub contDiffOn_const
  have hsm : ∀ t, 0 < t → t ≤ t₀ → ∀ j, ContDiffOn ℝ 2 (f t (b j) ∘ (A.chart jA).symm) U :=
    fun t h0 h1 j => (((H t h0 h1).2.2.1 (b j) jA).of_le h2').mono
      fun z hz => ⟨hz.1, hWb j hz.2⟩
  have hsmE : ∀ j, ∀ᶠ t in 𝓝[>] (0 : ℝ), ContDiffOn ℝ 2 (f t (b j) ∘ (A.chart jA).symm) U :=
    fun j => ev.mono fun t ht => hsm t ht.1 ht.2 j
  have hA := fun j => chart_C2_convergence A B hAB jA (b j) s ph hbd hph hW'o (hWb j)
    Set.inter_subset_right (fun t => f t (b j))
    (ev.mono fun t ht => (H t ht.1 ht.2).2.2.1 (b j)) (hc (b j)) hNc hNU
  have hAdd := fun j => tendstoC2On_add_small hUo hNU hNc hδ (hQ j) (hsmE j) (hA j).1
  choose M hM using fun j => (hA j).2
  choose C hC using fun j => (hAdd j).2
  let u : ℝ → Fin B.n → (Fin e → ℂ) → ℝ := fun t j z =>
    (f t (b j) ∘ (A.chart jA).symm) z + δ t * Q j z
  let M' : ℝ := ∑ j, (|C j| + |M j|)
  have hM'0 : ∀ j, |C j| + |M j| ≤ M' := fun j =>
    Finset.single_le_sum (f := fun j => |C j| + |M j|) (fun _ _ => by positivity) (Finset.mem_univ j)
  have hgrad : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ j, ∀ x ∈ N,
      ‖fderiv ℝ (u t j) x - fderiv ℝ p x‖ ≤ M' * δ t := by
    filter_upwards [ev, eventually_all.2 hM, eventually_all.2 hC] with t ht h1 h3 j x hx
    have hle := (H t ht.1 ht.2).1
    have hpos : 0 < δ t := ht.1.trans_le hle
    have a1 := h3 j x hx
    have a2 := h1 j x hx
    have a3 : C j * |δ t| ≤ |C j| * δ t := by
      rw [abs_of_pos hpos]
      exact mul_le_mul_of_nonneg_right (le_abs_self _) hpos.le
    have a4 : M j * t ≤ |M j| * δ t :=
      (mul_le_mul_of_nonneg_right (le_abs_self _) ht.1.le).trans
        (mul_le_mul_of_nonneg_left hle (abs_nonneg _))
    have a5 : (|C j| + |M j|) * δ t ≤ M' * δ t := mul_le_mul_of_nonneg_right (hM'0 j) hpos.le
    calc ‖fderiv ℝ (u t j) x - fderiv ℝ p x‖
        = ‖(fderiv ℝ (u t j) x - fderiv ℝ (f t (b j) ∘ (A.chart jA).symm) x) +
            (fderiv ℝ (f t (b j) ∘ (A.chart jA).symm) x - fderiv ℝ p x)‖ := by
          rw [sub_add_sub_cancel]
      _ ≤ _ := norm_add_le _ _
      _ ≤ C j * |δ t| + M j * t := add_le_add a1 a2
      _ ≤ M' * δ t := by nlinarith
  have hratio : Tendsto (fun t => (M' * δ t) ^ 2 / δ t) (𝓝[>] 0) (𝓝 0) := by
    have h0 : Tendsto (fun t => M' ^ 2 * δ t) (𝓝[>] 0) (𝓝 0) := by
      simpa using hδ.const_mul (M' ^ 2)
    refine h0.congr' ?_
    filter_upwards [ev] with t ht
    have hpos : 0 < δ t := ht.1.trans_le (H t ht.1 ht.2).1
    field_simp
  have hucd : ∀ t, 0 < t → t ≤ t₀ → ∀ j, ContDiffOn ℝ 2 (u t j) U :=
    fun t h0 h1 j => (hsm t h0 h1 j).add (contDiffOn_const.mul (hQ j))
  have hreg := GroundTheory.Heights₂.Heights.AnalyticLimit.RegularizedMaxConvergenceC2.proof (Fin B.n) U N p u δ
    (fun t => M' * δ t) hUo hNU hpC
    (ev.mono fun t ht => ⟨ht.1.trans_le (H t ht.1 ht.2).1, hucd t ht.1 ht.2⟩) hδ
    (fun j => (hAdd j).1) hgrad hratio
  have hevA : ∀ᶠ t in 𝓝[>] (0 : ℝ), ContDiffOn ℝ 2
      (fun x => ReciprocityTheory.AnForm.A.regMax (δ t) (fun j => u t j x) + δ t / 2) U := by
    filter_upwards [ev] with t ht
    have hpos : 0 < δ t := ht.1.trans_le (H t ht.1 ht.2).1
    exact (((ReciprocityTheory.AnForm.A.regMax_contDiff (ι := Fin B.n) hpos).of_le
      ReciprocityTheory.AnForm.A.two_le_inf).comp_contDiffOn (contDiffOn_pi.2 (hucd t ht.1 ht.2))).add
      contDiffOn_const
  have hfin := (tendstoC2On_add_small hUo hNU hNc hδ (Q := fun _ => K₀ - 1 / 2) contDiffOn_const
    hevA hreg).1
  refine tendstoC2On_congr hUo hNU ?_ hfin
  filter_upwards [ev] with t ht z hz
  obtain ⟨hle, hle1, -, hMb, hov⟩ := H t ht.1 ht.2
  have hpos : 0 < δ t := ht.1.trans_le hle
  have hr1 := hrep (f t) η (δ t) (Mb t) hpos hle1 (fun j => (hη j).2.2.1)
    (fun j => (hη j).2.2.2) hMb hov ((A.chart jA).symm z) hz.2.1
  have hu : (fun j => u t j z) = fun j => if j ∈ I then
      f t j ((A.chart jA).symm z) + 4 * δ t * η j ((A.chart jA).symm z)
      else f t k₀ ((A.chart jA).symm z) + 4 * δ t * η k₀ ((A.chart jA).symm z) - δ t := by
    funext j
    by_cases hj : j ∈ I
    · simp only [u, Q, b, hj, if_true, Function.comp_apply]; ring
    · simp only [u, Q, b, hj, if_false, Function.comp_apply]; ring
  simp only [Function.comp_apply]
  rw [hu, hr1]
  ring

end

end GlobalTheory.CompanionTheory.Ar.Giv.GlueC2

namespace GlobalTheory.CompanionTheory.Ar.Giv

open GlobalTheory.CompanionTheory.Ar.Giv.GlueC2

theorem regularization_glue_C2 : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (A B : FinHolAtlas e X) (Θ th : LocPot X) (s : X → X → ℂ) (ph : X → ℝ), A.Compatible B → (∀ x, ∃ j, x ∈ chartBall B j 1) → (∀ j, closedBall (0 : Fin e → ℂ) 2 ⊆ (B.chart j).target) → IsPotential A Θ → IsPosPot A Θ → IsPotential A th → IsClosed (bdry s) → A.SmoothOn (bdry s)ᶜ ph → ∃ K : ℝ, 0 < K ∧ ∀ (t₀ : ℝ) (δ : ℝ → ℝ) (f : ℝ → Fin B.n → X → ℝ), 0 < t₀ → Tendsto δ (𝓝[>] 0) (𝓝 0) → (∀ t, 0 < t → t ≤ t₀ → t ≤ δ t ∧ δ t ≤ 1 ∧ (∀ j, A.SmoothOn (chartBall B j (5 / 4)) (f t j)) ∧ (∃ Mb : ℝ, ∀ j, ∀ y ∈ chartBall B j (5 / 4), |f t j y| ≤ Mb) ∧ (∀ j, IsPshOn A (chartBall B j (5 / 4)) (th + LocPot.ofFun (f t j))) ∧ ∀ j k, ∀ y ∈ chartBall B j (5 / 4) ∩ chartBall B k (5 / 4), |f t j y - f t k y| ≤ δ t) → (∀ j, ∀ K' ⊆ ball (0 : Fin e → ℂ) (5 / 4) ∩ (B.chart j).symm ⁻¹' (bdry s)ᶜ, IsCompact K' → TendstoUniformlyOn (fun t => f t j ∘ (B.chart j).symm) (ph ∘ (B.chart j).symm) (𝓝[>] 0) K' ∧ TendstoUniformlyOn (fun t => fderiv ℝ (f t j ∘ (B.chart j).symm)) (fderiv ℝ (ph ∘ (B.chart j).symm)) (𝓝[>] 0) K' ∧ TendstoUniformlyOn (fun t => fderiv ℝ (fderiv ℝ (f t j ∘ (B.chart j).symm))) (fderiv ℝ (fderiv ℝ (ph ∘ (B.chart j).symm))) (𝓝[>] 0) K' ∧ ∃ M : ℝ, ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ z ∈ K', ‖fderiv ℝ (f t j ∘ (B.chart j).symm) z - fderiv ℝ (ph ∘ (B.chart j).symm) z‖ ≤ M * t) → ∃ F : ℝ → X → ℝ, (∀ t, 0 < t → t ≤ t₀ → A.Smooth (F t) ∧ IsPsh A (th + LocPot.ofFun (F t) + Θ.rsmul (K * δ t)) ∧ ∀ j, ∀ y ∈ chartBall B j (5 / 4), f t j y ≤ F t y ∧ F t y ≤ f t j y + K * δ t) ∧ IsRegFamilyC2 A s ph F := by
  intro e X _ _ _ A B Θ th s ph hAB hcov h2 hΘ hΘpos hth hbd hph
  obtain ⟨η, hη⟩ := glue_cutoff A B hAB h2
  by_cases hne : Nonempty (Fin B.n)
  swap
  · have hX : IsEmpty X := ⟨fun x => hne ⟨(hcov x).choose⟩⟩
    refine ⟨1, one_pos, fun t₀ δ f _ _ _ _ => ⟨fun _ _ => 0, fun t _ _ => ⟨?_, ?_, ?_⟩, ?_⟩⟩
    · exact fun k y _ => (hX.false ((A.chart k).symm y)).elim
    · exact fun x => (hX.false x).elim
    · exact fun j y _ => (hX.false y).elim
    · exact fun j => (hX.false ((A.chart j).symm 0)).elim
  obtain ⟨K₀, hK₀, hG⟩ := reg_glue_explicit A B Θ th hAB hcov h2 hΘ hΘpos hth η hη
  refine ⟨2 * K₀, by positivity, ?_⟩
  intro t₀ δ f ht₀ hδ H hc
  have hMbE : ∀ t, ∃ Mb : ℝ, 0 < t → t ≤ t₀ →
      ∀ j, ∀ y ∈ chartBall B j (5 / 4), |f t j y| ≤ Mb := by
    intro t
    by_cases ht : 0 < t ∧ t ≤ t₀
    · obtain ⟨Mb, h⟩ := (H t ht.1 ht.2).2.2.2.1
      exact ⟨Mb, fun _ _ => h⟩
    · exact ⟨0, fun h1 h3 => (ht ⟨h1, h3⟩).elim⟩
  choose Mb hMb using hMbE
  refine ⟨fun t y => ReciprocityTheory.AnForm.A.regMax (δ t)
    (fun j => glueArg B (f t) η (δ t) (Mb t) j y) + K₀ * δ t, ?_, ?_⟩
  · intro t h0 h1
    obtain ⟨hle, hle1, hsm, -, hps, hov⟩ := H t h0 h1
    have hpos : 0 < δ t := h0.trans_le hle
    obtain ⟨s1, s2, s3⟩ := hG (δ t) (Mb t) (f t) hpos hle1 hsm (hMb t h0 h1) hps hov
    refine ⟨fun k => (s1 k).add contDiffOn_const, s2 _, fun j y hy => ?_⟩
    have := abs_le.1 (s3 j y hy)
    constructor <;> linarith [this.1, this.2]
  · intro jA K hKs hKc
    have hO : IsOpen ((A.chart jA).target ∩ (A.chart jA).symm ⁻¹' (bdry s)ᶜ) :=
      (A.chart jA).isOpen_inter_preimage_symm hbd.isOpen_compl
    have hloc := fun z hz => glue_C2_local A B s ph hAB hcov h2 hbd hph η hη K₀ t₀ δ Mb f ht₀ hδ
      (fun t h0 h1 => ⟨(H t h0 h1).1, (H t h0 h1).2.1, (H t h0 h1).2.2.1, hMb t h0 h1,
        (H t h0 h1).2.2.2.2.2⟩) (fun j K' hK' hK'c => hc j K' hK' hK'c) jA z hz
    refine ⟨?_, ?_, ?_⟩
    · refine (tendstoLocallyUniformlyOn_iff_forall_isCompact hO).1
        (GroundTheory.Heights₂.Heights.AnalyticLimit.C2ConvergencePullback.tendstoLocallyUniformlyOn_of_nhds
          fun y hy => ?_) K hKs hKc
      obtain ⟨N, hN, h, -, -⟩ := hloc y hy
      exact ⟨N, hN, h⟩
    · refine (tendstoLocallyUniformlyOn_iff_forall_isCompact hO).1
        (GroundTheory.Heights₂.Heights.AnalyticLimit.C2ConvergencePullback.tendstoLocallyUniformlyOn_of_nhds
          fun y hy => ?_) K hKs hKc
      obtain ⟨N, hN, -, h, -⟩ := hloc y hy
      exact ⟨N, hN, h⟩
    · refine (tendstoLocallyUniformlyOn_iff_forall_isCompact hO).1
        (GroundTheory.Heights₂.Heights.AnalyticLimit.C2ConvergencePullback.tendstoLocallyUniformlyOn_of_nhds
          fun y hy => ?_) K hKs hKc
      obtain ⟨N, hN, -, -, h⟩ := hloc y hy
      exact ⟨N, hN, h⟩

end GlobalTheory.CompanionTheory.Ar.Giv
