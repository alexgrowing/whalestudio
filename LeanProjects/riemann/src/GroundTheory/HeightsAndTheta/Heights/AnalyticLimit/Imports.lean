import Mathlib
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.C2ConvergenceHypothesesNonempty
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.NormIteratedFDerivCompLeOfIsOpen
import GroundTheory.HeightsAndTheta.Heights.Regularisation.GlueCharts
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open Filter Topology Metric Set
open scoped ContDiff
open ReciprocityTheory.AnForm.A (Mollifier molli shrink)
open ReciprocityTheory.AnForm.M (FinHolAtlas)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (RegChartData RegCharts errorWithLinear)

noncomputable section

theorem ArgumentConvergenceC2.proof : ArgumentConvergenceC2.Statement := by
  intro X _ _ D A R ρ Cη η hη C hC j k L hL hLsub
  have hV'open : IsOpen (R.V' j) := (R.ψ j).isOpen_inter_preimage (R.isOpen_alt j)
  set O : Set (Fin D → ℂ) := (A.chart k).target ∩ (A.chart k).symm ⁻¹' (R.Yo ∩ R.V' j) with hO_def
  have hO : IsOpen O := (A.chart k).isOpen_inter_preimage_symm (R.isOpen_Yo.inter hV'open)
  have hOsrc : ∀ y ∈ O, (A.chart k).symm y ∈ (R.ψ j).source := fun y hy => hy.2.2.1

  obtain ⟨T, hT_def⟩ : ∃ T : (Fin D → ℂ) → (Fin D → ℂ), T = fun y => R.ψ j ((A.chart k).symm y) :=
    ⟨_, rfl⟩
  have hTy : ∀ y, T y = R.ψ j ((A.chart k).symm y) := fun y => by rw [hT_def]
  have hT : ∀ y ∈ O, ContDiffAt ℝ ∞ T y := by
    intro y hy
    have h := ((R.compat j k).1 y ⟨hy.1, hOsrc y hy⟩).restrictScalars (𝕜 := ℝ)
    rw [hT_def]
    exact h.contDiffAt
  have hTO : ContDiffOn ℝ ∞ T O := fun y hy => (hT y hy).contDiffWithinAt
  have hTc : ContinuousOn T O := hTO.continuousOn

  set P : Set (Fin D → ℂ) := ((R.ψ j).target ∩ (R.ψ j).symm ⁻¹' R.Yo) ∩ R.W j with hP_def
  have hP : IsOpen P := ((R.ψ j).isOpen_inter_preimage_symm R.isOpen_Yo).inter (R.isOpen_kappaOpenNeighbourhood j)
  have hu : ContDiffOn ℝ ∞ (R.u R.φ j) P := by
    intro z hz
    refine ContDiffAt.contDiffWithinAt ?_
    have hzs : (R.ψ j).symm z ∈ (R.ψ j).source := (R.ψ j).map_target hz.1.1
    have h1 := GroundTheory.Heights₂.Heights.Regular.contDiffAt_comp_symm_of_smoothOn (R.compat j)
      R.isOpen_Yo R.φ_smooth hz.1.2 hzs
    rw [(R.ψ j).right_inv hz.1.1] at h1
    exact ((R.q_smooth j).contDiffAt ((R.isOpen_kappaOpenNeighbourhood j).mem_nhds hz.2)).add h1
  have hTP : MapsTo T O P := by
    intro y hy
    rw [hTy]
    have hs := hOsrc y hy
    refine ⟨⟨(R.ψ j).map_source hs, ?_⟩, ?_⟩
    · rw [mem_preimage, (R.ψ j).left_inv hs]
      exact hy.2.1
    · exact R.closure_W'_subset j (subset_closure hy.2.2.2)
  have hfeq : ∀ y ∈ O, R.φ ((A.chart k).symm y) = R.u R.φ j (T y) - R.q j (T y) := by
    intro y hy
    simp only [RegCharts.u, hTy]
    rw [(R.ψ j).left_inv (hOsrc y hy)]
    ring
  have hF : ∀ t y, R.regArg R.φ ρ η C t j ((A.chart k).symm y) =
      molli ρ t (R.u R.φ j) (T y) - R.q j (T y) + 4 * errorWithLinear C t * η j ((A.chart k).symm y) := by
    intro t y
    rw [hTy]
    rfl
  have hf : ContDiffOn ℝ ∞ (fun y => R.φ ((A.chart k).symm y)) O :=
    (R.φ_smooth k).mono fun y hy => ⟨hy.1, hy.2.1⟩
  have hH : ContDiffOn ℝ ∞ (fun y => η j ((A.chart k).symm y)) O :=
    ((hη j).1 k).mono fun y hy => ⟨hy.1, hy.2.2⟩
  have hqT : ContDiffOn ℝ ∞ (fun y => R.q j (T y)) O :=
    (R.q_smooth j).comp hTO fun y hy => (hTP hy).2

  obtain ⟨δ, hδ, hδO⟩ := hL.exists_cthickening_subset_open hO hLsub
  have hKc : IsCompact (cthickening (δ / 2) L) := hL.cthickening
  have hKcO : cthickening (δ / 2) L ⊆ O := (cthickening_mono (by linarith) L).trans hδO
  have hLU : L ⊆ thickening (δ / 2) L := self_subset_thickening (by linarith) L
  have hUK : thickening (δ / 2) L ⊆ cthickening (δ / 2) L := thickening_subset_cthickening _ _
  have hK' : IsCompact (T '' cthickening (δ / 2) L) := hKc.image_of_continuousOn (hTc.mono hKcO)
  have hK'P : T '' cthickening (δ / 2) L ⊆ P := by
    rintro _ ⟨y, hy, rfl⟩
    exact hTP (hKcO hy)
  have hle : ∀ m : ℕ, (m : WithTop ℕ∞) ≤ ∞ := fun m => by exact_mod_cast le_top
  have h3 : (3 : WithTop ℕ∞) ≤ ∞ := hle 3
  have h2 : (2 : WithTop ℕ∞) ≤ ∞ := hle 2
  obtain ⟨C₀, ε₀, hε₀, hmol⟩ := ReciprocityTheory.AnForm.A.mollification_second_order D ρ P (T '' cthickening (δ / 2) L)
    (R.u R.φ j) hP (hu.of_le h3) hK' hK'P
  obtain ⟨BT, hBT⟩ := ArgumentConvergenceLemmas.exists_bound_iteratedFDeriv hO (hTO.of_le h2) hL hLsub
  obtain ⟨BH, hBH⟩ := ArgumentConvergenceLemmas.exists_bound_iteratedFDeriv hO (hH.of_le h2) hL hLsub
  set d : ℝ := max 1 BT with hd_def
  have hd1 : 1 ≤ d := le_max_left _ _
  set C₁ : ℝ := max C₀ 0 with hC₁_def
  have hC₁ : 0 ≤ C₁ := le_max_right _ _
  set B₁ : ℝ := max BH 0 with hB₁_def
  have hB₁ : 0 ≤ B₁ := le_max_right _ _
  set M : ℝ := 2 * C₁ * d ^ 2 + 4 * B₁ with hM_def

  have key : ∀ t ∈ Ioo 0 (min ε₀ (Real.exp (-1))),
      ContDiffOn ℝ 2 (fun y => R.regArg R.φ ρ η C t j ((A.chart k).symm y)) (thickening (δ / 2) L) ∧
      ∀ y ∈ L, ∀ n : ℕ, n ≤ 2 → ‖iteratedFDeriv ℝ n (fun y =>
        R.regArg R.φ ρ η C t j ((A.chart k).symm y) - R.φ ((A.chart k).symm y)) y‖ ≤
          M * (t + errorWithLinear C t) := by
    rintro t ⟨ht0, ht⟩
    have htε : t < ε₀ := ht.trans_le (min_le_left _ _)
    have hte : t < Real.exp (-1) := ht.trans_le (min_le_right _ _)
    have he1 : 0 < errorWithLinear C t := ArgumentConvergenceLemmas.logErrorBound_pos hC ht0 hte
    have hShr : IsOpen (shrink P t) := ReciprocityTheory.AnForm.A.isOpen_shrink hP ht0
    have hShrP : shrink P t ⊆ P := fun z hz => hz (mem_closedBall_self ht0.le)
    have hm : ContDiffOn ℝ ∞ (molli ρ t (R.u R.φ j)) (shrink P t) := fun z hz =>
      (ArgumentConvergenceLemmas.molli_contDiffAt ρ hP hu.continuousOn ht0 hz).contDiffWithinAt
    have hK'S : ∀ y ∈ cthickening (δ / 2) L, T y ∈ shrink P t := fun y hy =>
      (hmol t ht0 htε (T y) ⟨y, hy, rfl⟩).1
    set s : Set (Fin D → ℂ) := O ∩ T ⁻¹' shrink P t with hs_def
    have hs : IsOpen s := hTc.isOpen_inter_preimage hO hShr
    have hKs : cthickening (δ / 2) L ⊆ s := fun y hy => ⟨hKcO hy, hK'S y hy⟩
    have hTs : ContDiffOn ℝ ∞ T s := hTO.mono inter_subset_left
    have hmT : ContDiffOn ℝ ∞ (fun y => molli ρ t (R.u R.φ j) (T y)) s :=
      hm.comp hTs fun y hy => hy.2
    have hFs : ContDiffOn ℝ ∞ (fun y => R.regArg R.φ ρ η C t j ((A.chart k).symm y)) s := by
      have : ContDiffOn ℝ ∞ (fun y => molli ρ t (R.u R.φ j) (T y) - R.q j (T y) +
          4 * errorWithLinear C t * η j ((A.chart k).symm y)) s :=
        (hmT.sub (hqT.mono inter_subset_left)).add
          (contDiffOn_const.mul (hH.mono inter_subset_left))
      exact this.congr fun y _ => hF t y
    refine ⟨(hFs.of_le h2).mono (hUK.trans hKs), ?_⟩
    intro y hyL n hn
    have hyO : y ∈ O := hLsub hyL
    have hyK : y ∈ cthickening (δ / 2) L := self_subset_cthickening L hyL
    have hys : y ∈ s := hKs hyK
    set G : (Fin D → ℂ) → ℝ := fun z => molli ρ t (R.u R.φ j) z - R.u R.φ j z with hG_def
    have hGs : ContDiffOn ℝ ∞ G (shrink P t) := hm.sub (hu.mono hShrP)
    have heq : (fun y => R.regArg R.φ ρ η C t j ((A.chart k).symm y) - R.φ ((A.chart k).symm y))
        =ᶠ[𝓝 y] (G ∘ T) + (4 * errorWithLinear C t) • (fun y => η j ((A.chart k).symm y)) := by
      filter_upwards [hO.mem_nhds hyO] with y' hy'
      simp only [Pi.add_apply, Function.comp, Pi.smul_apply, smul_eq_mul, hG_def]
      rw [hF, hfeq y' hy']
      ring
    have hn' : (n : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
    have hGT : ContDiffAt ℝ n (G ∘ T) y :=
      ((hGs.comp hTs fun y hy => hy.2).contDiffAt (hs.mem_nhds hys)).of_le hn'
    have hHy : ContDiffAt ℝ n (fun y => η j ((A.chart k).symm y)) y :=
      (hH.contDiffAt (hO.mem_nhds hyO)).of_le hn'
    have hcH : ContDiffAt ℝ n ((4 * errorWithLinear C t) • fun y => η j ((A.chart k).symm y)) y :=
      hHy.const_smul (4 * errorWithLinear C t)
    rw [(heq.iteratedFDeriv ℝ n).eq_of_nhds, iteratedFDeriv_add_apply hGT hcH,
      iteratedFDeriv_const_smul_apply hHy]

    have hmb := hmol t ht0 htε (T y) ⟨y, hyK, rfl⟩
    have hGC : ∀ i : ℕ, i ≤ 2 → ‖iteratedFDeriv ℝ i G (T y)‖ ≤ C₁ * t := by
      have hCt : C₀ * t ≤ C₁ * t := mul_le_mul_of_nonneg_right (le_max_left _ _) ht0.le
      obtain ⟨e0, e1, e2⟩ := ArgumentConvergenceLemmas.norm_iteratedFDeriv_sub_eq hShr (hm.of_le h2)
        ((hu.mono hShrP).of_le h2) (hK'S y hyK)
      intro i hi
      interval_cases i
      · rw [e0, Real.norm_eq_abs]
        exact hmb.2.1.trans hCt
      · rw [e1]
        exact hmb.2.2.1.trans hCt
      · rw [e2]
        exact hmb.2.2.2.trans hCt
    have hTd : ∀ i : ℕ, 1 ≤ i → i ≤ 2 → ‖iteratedFDeriv ℝ i T y‖ ≤ d ^ i := by
      intro i hi1 hi2
      interval_cases i
      · rw [pow_one]
        exact (hBT 1 (by norm_num) y hyL).trans (le_max_right _ _)
      · exact (hBT 2 le_rfl y hyL).trans ((le_max_right _ _).trans (le_self_pow₀ hd1 (by norm_num)))
    have hGb : ‖iteratedFDeriv ℝ n (G ∘ T) y‖ ≤ n.factorial * (C₁ * t) * d ^ n :=
      ArgumentConvergenceLemmas.norm_iteratedFDeriv_comp_le_of_isOpen hs hShr (hGs.of_le h2) (hTs.of_le h2)
        (fun y hy => hy.2) hys hn hGC hTd
    have hfac : (n.factorial : ℝ) ≤ 2 := by
      interval_cases n <;> norm_num [Nat.factorial]
    have hpow : d ^ n ≤ d ^ 2 := pow_le_pow_right₀ hd1 hn
    have hGb' : ‖iteratedFDeriv ℝ n (G ∘ T) y‖ ≤ 2 * C₁ * d ^ 2 * t := by
      have hCt0 : 0 ≤ C₁ * t := mul_nonneg hC₁ ht0.le
      calc ‖iteratedFDeriv ℝ n (G ∘ T) y‖ ≤ n.factorial * (C₁ * t) * d ^ n := hGb
        _ ≤ 2 * (C₁ * t) * d ^ 2 :=
          mul_le_mul (mul_le_mul_of_nonneg_right hfac hCt0) hpow (by positivity) (by positivity)
        _ = 2 * C₁ * d ^ 2 * t := by ring

    have hHb : ‖(4 * errorWithLinear C t) • iteratedFDeriv ℝ n (fun y => η j ((A.chart k).symm y)) y‖ ≤
        4 * B₁ * errorWithLinear C t := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
      have := (hBH n hn y hyL).trans (le_max_left BH 0)
      nlinarith
    have hsum := norm_add_le (iteratedFDeriv ℝ n (G ∘ T) y)
      ((4 * errorWithLinear C t) • iteratedFDeriv ℝ n (fun y => η j ((A.chart k).symm y)) y)
    have hx1 : 0 ≤ 2 * C₁ * d ^ 2 * errorWithLinear C t := by positivity
    have hx2 : 0 ≤ 4 * B₁ * t := by positivity
    have hexp : M * (t + errorWithLinear C t) = 2 * C₁ * d ^ 2 * t + 2 * C₁ * d ^ 2 * errorWithLinear C t +
        4 * B₁ * t + 4 * B₁ * errorWithLinear C t := by
      rw [hM_def]; ring
    linarith

  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), t ∈ Ioo 0 (min ε₀ (Real.exp (-1))) :=
    Ioo_mem_nhdsGT (lt_min hε₀ (Real.exp_pos _))
  have hβ : Tendsto (fun t => M * (t + errorWithLinear C t)) (𝓝[>] 0) (𝓝 0) := by
    have h := ((tendsto_id.mono_left nhdsWithin_le_nhds).add (ArgumentConvergenceLemmas.tendsto_logErrorBound_nhdsWithin C)).const_mul M
    simpa using h
  have hfU : ContDiffOn ℝ 2 (fun y => R.φ ((A.chart k).symm y)) (thickening (δ / 2) L) :=
    (hf.of_le h2).mono (hUK.trans hKcO)
  have three : ∀ t ∈ Ioo 0 (min ε₀ (Real.exp (-1))), ∀ y ∈ L,
      ‖R.regArg R.φ ρ η C t j ((A.chart k).symm y) - R.φ ((A.chart k).symm y)‖ ≤ M * (t + errorWithLinear C t) ∧
      ‖fderiv ℝ (fun y' => R.regArg R.φ ρ η C t j ((A.chart k).symm y')) y -
          fderiv ℝ (fun y' => R.φ ((A.chart k).symm y')) y‖ ≤ M * (t + errorWithLinear C t) ∧
      ‖fderiv ℝ (fderiv ℝ (fun y' => R.regArg R.φ ρ η C t j ((A.chart k).symm y'))) y -
          fderiv ℝ (fderiv ℝ (fun y' => R.φ ((A.chart k).symm y'))) y‖ ≤ M * (t + errorWithLinear C t) := by
    intro t ht y hy
    obtain ⟨e0, e1, e2⟩ := ArgumentConvergenceLemmas.norm_iteratedFDeriv_sub_eq isOpen_thickening (key t ht).1 hfU
      (hLU hy)
    refine ⟨?_, ?_, ?_⟩
    · rw [← e0]; exact (key t ht).2 y hy 0 (by norm_num)
    · rw [← e1]; exact (key t ht).2 y hy 1 (by norm_num)
    · rw [← e2]; exact (key t ht).2 y hy 2 le_rfl
  refine ⟨thickening (δ / 2) L, isOpen_thickening, hLU, hfU, ?_, ⟨?_, ?_, ?_⟩, M, ?_⟩
  · filter_upwards [hev] with t ht using (key t ht).1
  · refine ArgumentConvergenceLemmas.tendstoUniformlyOn_of_norm_le hβ ?_
    filter_upwards [hev] with t ht y hy using (three t ht y hy).1
  · refine ArgumentConvergenceLemmas.tendstoUniformlyOn_of_norm_le (α := (Fin D → ℂ) →L[ℝ] ℝ) hβ ?_
    filter_upwards [hev] with t ht y hy using (three t ht y hy).2.1
  · refine ArgumentConvergenceLemmas.tendstoUniformlyOn_of_norm_le
      (α := (Fin D → ℂ) →L[ℝ] (Fin D → ℂ) →L[ℝ] ℝ) hβ ?_
    filter_upwards [hev] with t ht y hy using (three t ht y hy).2.2
  · filter_upwards [hev] with t ht y hy using (three t ht y hy).2.1

end

end GroundTheory.Heights₂.Heights.AnalyticLimit
