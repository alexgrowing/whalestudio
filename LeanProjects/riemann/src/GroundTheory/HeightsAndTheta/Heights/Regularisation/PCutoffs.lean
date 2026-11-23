import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Regularisation.Statements
import ReciprocityTheory.AnalyticForms.PotentialTheory.HessCEqZeroOfEventuallyEqZero
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Regular

open Metric Set Filter Topology
open scoped ContDiff Manifold
open ReciprocityTheory.AnForm (levi)
open ReciprocityTheory.AnForm.M (FinHolAtlas IsCompatChart)
open ReciprocityTheory.AnForm.M.PLAux (chartPush chartPush_eq_zero isCompact_symm_image smooth_chartPush
  contDiffOn_compat)

noncomputable section

theorem exists_smooth_bump_of_isCompact {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {K V : Set E} (hK : IsCompact K) (hV : IsOpen V) (hKV : K ⊆ V) :
    ∃ g : E → ℝ, ContDiff ℝ ∞ g ∧ (∀ y, 0 ≤ g y ∧ g y ≤ 1) ∧ (∀ y ∈ K, g y = 1) ∧
      IsCompact (tsupport g) ∧ tsupport g ⊆ V := by
  obtain ⟨W, hWo, hKW, hWV, hWc⟩ := exists_open_between_and_isCompact_closure hK hV hKV
  have hd : Disjoint Wᶜ K := Set.disjoint_compl_left_iff_subset.2 hKW
  obtain ⟨f, hf, hrange, h0, h1⟩ := exists_contMDiff_zero_iff_one_iff_of_isClosed
    (I := 𝓘(ℝ, E)) (n := ⊤) hWo.isClosed_compl hK.isClosed hd
  have hsupp : tsupport f ⊆ closure W := by
    refine closure_mono fun y hy => ?_
    by_contra hyW
    exact hy ((h0 y).1 hyW)
  refine ⟨f, contMDiff_iff_contDiff.1 hf, fun y => hrange ⟨y, rfl⟩, fun y hy => (h1 y).1 hy,
    hWc.of_isClosed_subset (isClosed_tsupport f) hsupp, hsupp.trans hWV⟩

theorem levi_lower_bound_of_isCompact {D : ℕ} {f : (Fin D → ℂ) → ℝ} {U K : Set (Fin D → ℂ)}
    (hU : IsOpen U) (hf : ContDiffOn ℝ 2 f U) (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ K, ∀ w, -C * ‖w‖ ^ 2 ≤ levi f y w := by
  have hS : IsCompact (K ×ˢ sphere (0 : Fin D → ℂ) 1) := hK.prod (isCompact_sphere 0 1)
  have hc : ContinuousOn (fun p : (Fin D → ℂ) × (Fin D → ℂ) => levi f p.1 p.2)
      (K ×ˢ sphere (0 : Fin D → ℂ) 1) :=
    (ReciprocityTheory.AnForm.continuousOn_levi hU hf).mono (prod_mono hKU (subset_univ _))
  obtain ⟨C, hC⟩ := hS.exists_bound_of_continuousOn hc
  refine ⟨max C 0, le_max_right _ _, fun y hy w => ?_⟩
  by_cases hw : w = 0
  · subst hw
    simp [ReciprocityTheory.AnForm.levi_zero]
  have hn : 0 < ‖w‖ := norm_pos_iff.2 hw
  have hu : ‖‖w‖⁻¹ • w‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_norm, inv_mul_cancel₀ hn.ne']
  have hb := hC (y, ‖w‖⁻¹ • w) ⟨hy, by simpa using hu⟩
  have hb' : -max C 0 ≤ levi f y (‖w‖⁻¹ • w) := by
    have := (abs_le.1 (Real.norm_eq_abs _ ▸ hb)).1
    linarith [le_max_left C 0]
  have hw' : w = ‖w‖ • (‖w‖⁻¹ • w) := by
    rw [smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
  rw [hw', ReciprocityTheory.AnForm.levi_smul_dir]
  have h2 : 0 ≤ ‖w‖ ^ 2 := by positivity
  have := mul_le_mul_of_nonneg_left hb' h2
  have hnn : ‖‖w‖ • (‖w‖⁻¹ • w)‖ = ‖w‖ := by rw [← hw']
  rw [hnn]
  linarith

theorem CutoffsExist.proof : CutoffsExist.Statement := by
  intro X _ _ _ D A P
  have hb : ∀ j, ∃ g : (Fin D → ℂ) → ℝ, ContDiff ℝ ∞ g ∧ (∀ y, 0 ≤ g y ∧ g y ≤ 1) ∧
      (∀ y ∈ P.chart j '' closure (P.inner j), g y = 1) ∧ IsCompact (tsupport g) ∧
      tsupport g ⊆ P.chartMid j := by
    intro j
    have hcl : closure (P.inner j) ⊆ (P.chart j).source :=
      (P.closure_inner j).trans (P.mid_subset_source j)
    refine exists_smooth_bump_of_isCompact
      (isClosed_closure.isCompact.image_of_continuousOn ((P.chart j).continuousOn.mono hcl))
      ((P.chart j).continuousOn_symm.isOpen_inter_preimage (P.chart j).open_target
        (P.isOpen_mid j)) ?_
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨(P.chart j).map_source (hcl hx), by
      rw [mem_preimage, (P.chart j).left_inv (hcl hx)]; exact P.closure_inner j hx⟩
  choose g hgs hg01 hg1 hgc hgt using hb
  have hgt' : ∀ j, tsupport (g j) ⊆ (P.chart j).target := fun j => (hgt j).trans inter_subset_left
  have hcp : ∀ j x, 0 ≤ chartPush (P.chart j) (g j) x ∧ chartPush (P.chart j) (g j) x ≤ 1 := by
    intro j x
    unfold chartPush
    by_cases hx : x ∈ (P.chart j).source
    · rw [indicator_of_mem hx]; exact hg01 j _
    · rw [indicator_of_notMem hx]; exact ⟨le_rfl, zero_le_one⟩
  have hsm : ∀ j, A.Smooth (fun x => chartPush (P.chart j) (g j) x - 1) := by
    intro j a
    exact ContDiffOn.sub (f := chartPush (P.chart j) (g j) ∘ (A.chart a).symm)
      (smooth_chartPush (P.compat j) (hgs j) (hgc j) (hgt' j) a) contDiffOn_const
  have hC : ∀ j k, ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ P.chart k '' closure (P.mid k), ∀ w,
      -C * ‖w‖ ^ 2 ≤ levi ((fun x => chartPush (P.chart j) (g j) x - 1) ∘ (P.chart k).symm) y w := by
    intro j k
    have h := contDiffOn_compat (P.compat k) isOpen_univ (hsm j)
    rw [preimage_univ, inter_univ] at h
    refine levi_lower_bound_of_isCompact (P.chart k).open_target (h.of_le (WithTop.coe_le_coe.2 le_top))
      (isClosed_closure.isCompact.image_of_continuousOn
        ((P.chart k).continuousOn.mono (P.closure_mid k))) ?_
    rintro _ ⟨x, hx, rfl⟩
    exact (P.chart k).map_source (P.closure_mid k hx)
  choose C hC0 hC using hC
  refine ⟨fun j x => chartPush (P.chart j) (g j) x - 1, ∑ j, ∑ k, C j k, ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · intro j a
    exact (hsm j a).mono (inter_subset_inter_right _ (preimage_mono (subset_univ _)))
  · intro j x _
    constructor <;> linarith [hcp j x]
  · intro j x hx
    have hs : x ∈ (P.chart j).source := P.mid_subset_source j (P.inner_subset_mid j hx)
    have h1 : chartPush (P.chart j) (g j) x = 1 := by
      unfold chartPush
      rw [indicator_of_mem hs]
      exact hg1 j _ ⟨x, subset_closure hx, rfl⟩
    simp [h1]
  · intro j
    refine ⟨(P.chart j).symm '' tsupport (g j), (isCompact_symm_image (hgc j) (hgt' j)).isClosed,
      ?_, ?_⟩
    · rintro _ ⟨y, hy, rfl⟩
      exact (hgt j hy).2
    · intro x hx
      simp [chartPush_eq_zero (P.chart j) hx.2]
  · intro j k x hx w
    have h := hC j k (P.chart k x) ⟨x, subset_closure hx.2, rfl⟩ w
    have hle : C j k ≤ ∑ j, ∑ k, C j k :=
      (Finset.single_le_sum (fun k _ => hC0 j k) (Finset.mem_univ k)).trans
        (Finset.single_le_sum (f := fun j => ∑ k, C j k)
          (fun j _ => Finset.sum_nonneg fun k _ => hC0 j k) (Finset.mem_univ j))
    have h2 : 0 ≤ ‖w‖ ^ 2 := by positivity
    nlinarith

end

end GroundTheory.Heights₂.Heights.Regular
