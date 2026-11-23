import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.IntegralMem
import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.BlkUInvVal

noncomputable section

open MeasureTheory Matrix GlobalTheory.CuspGeneric Topology
open scoped ContDiff

namespace PositivityTheory.jumpWindows

open CornerBlockIndex in
theorem mirabolic_induction_step_exists : S2 → S3 → S5 → S6 → S8 → MirabolicColumnBlock → S7 := by
  intro h2 h3 h5 h6 h8 h10 ι _ a X _ _ _ ρ hρ m hm χ hχc hχn hχnd U hU
  obtain ⟨l, hl⟩ := h8 ι χ hχc hχn
  have hβ : ∀ y : CornerBlockIndex.V ι a m, (∀ x, CornerBlockIndex.bet (a := a) (m := m) l x y = 0) → y = 0 :=
    CornerBlockIndex.bet_nondeg hm hχnd hl
  let μ : Measure (CornerBlockIndex.V ι a m) := Measure.addHaar
  obtain ⟨c, hc0, hc⟩ := h5 (CornerBlockIndex.V ι a m) μ (CornerBlockIndex.bet l) hβ
  obtain ⟨f, hfW, hfc, hfd, hfr, hfe⟩ :=
    exists_contDiff_tsupport_subset (n := ⊤) (CornerBlockIndex.nhds_good hm hU)
  let η : CornerBlockIndex.V ι a m → ℂ := fun x => (f x : ℂ)
  have hηd : ContDiff ℝ ∞ η := Complex.ofRealCLM.contDiff.comp hfd
  have hηc : HasCompactSupport η := hfc.comp_left Complex.ofReal_zero
  have hηO : tsupport η ⊆ CornerBlockIndex.O ι hm :=
    (tsupport_comp_subset Complex.ofReal_zero f).trans (hfW.trans Set.inter_subset_left)
  have hfO : tsupport f ⊆ CornerBlockIndex.O ι hm := hfW.trans Set.inter_subset_left
  have hne : ∀ x, η x ≠ 0 → x ∈ tsupport f := by
    intro x hx
    apply subset_tsupport
    intro h0
    apply hx
    simp [η, h0]
  refine ⟨fun h => η (CornerBlockIndex.xi hm h), fun h => h * (CornerBlockIndex.uM hm (CornerBlockIndex.xi hm h))⁻¹, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [η, CornerBlockIndex.xi_one, hfe]
  · simp [CornerBlockIndex.xi_one, CornerBlockIndex.uM_e]
  · intro h hb hη
    exact CornerBlockIndex.mir_mul hm hb (hfO (hne _ hη))
  · intro h
    exact ⟨f (CornerBlockIndex.xi hm h), (hfr ⟨_, rfl⟩).1, rfl⟩
  · refine ⟨CornerBlockIndex.uM hm '' tsupport f, ?_, ?_, ?_, ?_⟩
    · exact hfc.isCompact.image_of_continuousOn ((CornerBlockIndex.contOn_uM hm).mono hfO)
    · rintro _ ⟨x, hx, rfl⟩
      exact (hfW hx).2
    · rintro _ ⟨x, _, rfl⟩
      exact CornerBlockIndex.blk_uM hm x
    · intro h _ hη
      exact ⟨_, ⟨_, hne _ hη, rfl⟩, by group⟩
  · intro v hv
    let F : CornerBlockIndex.V ι a m → X := fun x => η x • orb ρ v (CornerBlockIndex.sI hm x)
    have hFd : ContDiff ℝ ∞ F := CornerBlockIndex.cd_cut hm hv hηd hηO
    have hFc : HasCompactSupport F := hηc.smul_right
    obtain ⟨𝒢, h𝒢, hG⟩ := h6 ι a X ρ hρ (CornerBlockIndex.V ι a m) μ (CornerBlockIndex.bet l) hβ (CornerBlockIndex.O ι hm) (CornerBlockIndex.sI hm)
      (CornerBlockIndex.sM hm) (CornerBlockIndex.isOpen_O hm) (CornerBlockIndex.cd_sI hm) (CornerBlockIndex.cd_sM hm).contDiffOn
      (fun x hx => CornerBlockIndex.sI_mul_sM hm hx)
    have hGmem : FT μ (CornerBlockIndex.bet l) F ∈ 𝒢 := hG η v hηd hηc hηO hv
    obtain ⟨hint, hsm⟩ := h3 ι a X ρ hρ (CornerBlockIndex.V ι a m) μ (fun y => blkU y) (CornerBlockIndex.Lb hm)
      (CornerBlockIndex.blkU_val hm) (CornerBlockIndex.blkU_inv_val hm) 𝒢 h𝒢 _ hGmem
    have hFint : ∀ y, Integrable (fun x => Complex.exp (-↑((CornerBlockIndex.bet l x) y) * Complex.I) • F x) μ := by
      intro y
      apply Continuous.integrable_of_hasCompactSupport
      · exact Continuous.smul (by fun_prop) hFd.continuous
      · exact hFc.smul_left
    refine ⟨c⁻¹ • ∫ y, ρ (blkU y) (FT μ (CornerBlockIndex.bet l) F y) ∂μ, (h2 ι a X ρ hρ).2.2.1 _ _ hsm, ?_⟩
    intro Y hYc hYinv hvY
    have hFY : ∀ x, F x ∈ Y := by
      intro x
      apply Y.smul_mem
      unfold orb
      split_ifs
      · exact hYinv _ _ hvY
      · exact Y.zero_mem
    have hGY : ∀ y, FT μ (CornerBlockIndex.bet l) F y ∈ Y := fun y =>
      CornerBlockIndex.integral_mem hYc (hFint y) (fun x => Y.smul_mem _ (hFY x))
    refine ⟨Y.smul_mem _ (CornerBlockIndex.integral_mem hYc hint (fun y => hYinv _ _ (hGY y))), ?_⟩
    intro Λ hΛ h hb
    let L : X →L[ℂ] ℂ := Λ.comp (ρ h)
    let φ : CornerBlockIndex.V ι a m → ℂ := fun x => L (F x)
    have hφd : ContDiff ℝ ∞ φ := (L.restrictScalars ℝ).contDiff.comp hFd
    have hφc : HasCompactSupport φ := hFc.comp_left (map_zero L)
    have hkey : ∀ y, L (ρ (blkU y) (FT μ (CornerBlockIndex.bet l) F y)) =
        Complex.exp (↑((CornerBlockIndex.bet l (CornerBlockIndex.xi hm h)) y) * Complex.I) * FT μ (CornerBlockIndex.bet l) φ y := by
      intro y
      obtain ⟨y', hcomm, hy'⟩ := (h10 (ι → ℂ) a (m + 1)).2.2.2.2.2.2.2 h hb y
      have ht0 : ((CornerBlockIndex.t0 hm : UnipotentBlockColumnIndex a (m + 1) (m + 1)) : Fin a × Fin a).1 = CornerBlockIndex.mm hm :=
        (CornerBlockIndex.block_index_eq_corner_iff hm _).1 rfl
      have e1 : L (ρ (blkU y) (FT μ (CornerBlockIndex.bet l) F y)) =
          Λ (ρ (blkU y') (ρ h (FT μ (CornerBlockIndex.bet l) F y))) := by
        simp only [L, ContinuousLinearMap.comp_apply]
        rw [← ContinuousLinearMap.mul_apply, ← map_mul, hcomm, map_mul, ContinuousLinearMap.mul_apply]
      have e2 : Λ (ρ h (FT μ (CornerBlockIndex.bet l) F y)) = FT μ (CornerBlockIndex.bet l) φ y := by
        show L (∫ x, Complex.exp (-↑((CornerBlockIndex.bet l x) y) * Complex.I) • F x ∂μ) = _
        rw [← L.integral_comp_comm (hFint y)]
        unfold FT
        congr 1
        funext x
        exact L.map_smul _ _
      rw [e1, hΛ _ (hYinv _ _ (hGY y)), e2, CornerBlockIndex.lastE_eq hm, hy', ht0, hl, CornerBlockIndex.bet_apply]
      rfl
    have hmain : Λ (ρ h (c⁻¹ • ∫ y, ρ (blkU y) (FT μ (CornerBlockIndex.bet l) F y) ∂μ)) = φ (CornerBlockIndex.xi hm h) := by
      have : Λ (ρ h (c⁻¹ • ∫ y, ρ (blkU y) (FT μ (CornerBlockIndex.bet l) F y) ∂μ)) =
          c⁻¹ * ∫ y, L (ρ (blkU y) (FT μ (CornerBlockIndex.bet l) F y)) ∂μ := by
        rw [L.integral_comp_comm hint]
        simp only [L, ContinuousLinearMap.comp_apply, map_smul, smul_eq_mul]
      rw [this]
      simp_rw [hkey]
      rw [hc φ hφd hφc (CornerBlockIndex.xi hm h)]
      field_simp
    rw [hmain]
    show L (η (CornerBlockIndex.xi hm h) • orb ρ v (CornerBlockIndex.sI hm (CornerBlockIndex.xi hm h))) = _
    rw [map_smul, smul_eq_mul]
    by_cases h0 : η (CornerBlockIndex.xi hm h) = 0
    · simp [h0]
    · congr 1
      rw [CornerBlockIndex.orb_sI hm ρ v (hfO (hne _ h0))]
      simp only [L, ContinuousLinearMap.comp_apply, map_mul, ContinuousLinearMap.mul_apply]

end PositivityTheory.jumpWindows

end
