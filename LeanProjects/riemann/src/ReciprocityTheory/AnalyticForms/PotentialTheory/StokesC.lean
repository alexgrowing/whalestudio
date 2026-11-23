import ReciprocityTheory.AnalyticForms.PotentialTheory.StokesB

namespace ReciprocityTheory.AnForm.M

open MeasureTheory FinHolAtlas Filter Topology Set
open scoped ContDiff

noncomputable section

variable {e : ℕ} {X : Type} [TopologicalSpace X]

theorem st_hessC_congr {D : ℕ} {f g : (Fin D → ℂ) → ℝ} {y : Fin D → ℂ} (h : f =ᶠ[𝓝 y] g) :
    hessC f y = hessC g y := by
  have h2 : fderiv ℝ (fderiv ℝ f) y = fderiv ℝ (fderiv ℝ g) y :=
    (h.fderiv (𝕜 := ℝ)).fderiv_eq
  unfold hessC
  rw [h2]

private lemma maDens_congr_of_hessC_eq {D : ℕ} {F F' : Fin D → (Fin D → ℂ) → ℝ} {y : Fin D → ℂ}
    (h : ∀ k, hessC (F k) y = hessC (F' k) y) : maDens F y = maDens F' y := by
  unfold maDens
  simp only [h]

private lemma two_le_infty_withTop : (2 : WithTop ℕ∞) ≤ ∞ := by
  first
    | exact WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤)
    | exact_mod_cast le_top
    | simp

private lemma three_le_infty_withTop : (3 : WithTop ℕ∞) ≤ ∞ := by
  first
    | exact WithTop.coe_le_coe.2 (le_top : (3 : ℕ∞) ≤ ⊤)
    | exact_mod_cast le_top
    | simp

private lemma contDiffAt_two_re_of_analyticAt {D : ℕ} {K : (Fin D → ℂ) → ℂ} {z : Fin D → ℂ}
    (hK : AnalyticAt ℂ K z) : ContDiffAt ℝ 2 (fun w => (K w).re) z :=
  Complex.reCLM.contDiff.contDiffAt.comp z (hK.contDiffAt.restrict_scalars ℝ)

private lemma hessC_add_potential {D : ℕ} {f g : (Fin D → ℂ) → ℝ} {y : Fin D → ℂ}
    (hf : ∀ᶠ z in 𝓝 y, ContDiffAt ℝ 2 f z) (hg : ∀ᶠ z in 𝓝 y, ContDiffAt ℝ 2 g z) :
    hessC (fun z => f z + g z) y = hessC f y + hessC g y := by
  have hd : fderiv ℝ (fun z => f z + g z) =ᶠ[𝓝 y] fun z => fderiv ℝ f z + fderiv ℝ g z := by
    filter_upwards [hf, hg] with z h1 h2
    exact fderiv_add (h1.differentiableAt (by first | norm_num | exact one_le_two | simp))
      (h2.differentiableAt (by first | norm_num | exact one_le_two | simp))
  have hf2 : DifferentiableAt ℝ (fderiv ℝ f) y :=
    (hf.self_of_nhds.fderiv_right (m := 1)
      (by first | norm_num | exact le_of_eq one_add_one_eq_two | simp)).differentiableAt (by first | exact one_ne_zero | norm_num | simp)
  have hg2 : DifferentiableAt ℝ (fderiv ℝ g) y :=
    (hg.self_of_nhds.fderiv_right (m := 1)
      (by first | norm_num | exact le_of_eq one_add_one_eq_two | simp)).differentiableAt (by first | exact one_ne_zero | norm_num | simp)
  have hH : fderiv ℝ (fderiv ℝ (fun z => f z + g z)) y =
      fderiv ℝ (fderiv ℝ f) y + fderiv ℝ (fderiv ℝ g) y := by
    rw [hd.fderiv_eq]
    exact fderiv_add hf2 hg2
  ext i k
  simp only [hessC, hH, Matrix.add_apply, ContinuousLinearMap.add_apply]
  push_cast
  ring

private lemma hessC_re_of_analyticAt {D : ℕ} {H : (Fin D → ℂ) → ℂ} {y : Fin D → ℂ}
    (hH : AnalyticAt ℂ H y) : hessC (fun z => (H z).re) y = 0 := by
  have h1 : fderiv ℝ (fun z => (H z).re) =ᶠ[𝓝 y] fun z =>
      (ContinuousLinearMap.compL ℝ (Fin D → ℂ) ℂ ℝ Complex.reCLM)
        ((ContinuousLinearMap.restrictScalarsL ℂ (Fin D → ℂ) ℂ ℝ ℝ) (fderiv ℂ H z)) := by
    filter_upwards [hH.eventually_analyticAt] with z hz
    have hd : HasFDerivAt (fun w => (H w).re)
        (Complex.reCLM.comp ((fderiv ℂ H z).restrictScalars ℝ)) z :=
      Complex.reCLM.hasFDerivAt.comp z (hz.differentiableAt.hasFDerivAt.restrictScalars ℝ)
    rw [hd.fderiv]
    first
      | rfl
      | (ext v; simp)
  have hD : HasFDerivAt (fderiv ℂ H) ((fderiv ℂ (fderiv ℂ H) y).restrictScalars ℝ) y :=
    hH.fderiv.differentiableAt.hasFDerivAt.restrictScalars ℝ
  have h2 : HasFDerivAt (fun z => (ContinuousLinearMap.compL ℝ (Fin D → ℂ) ℂ ℝ Complex.reCLM)
        ((ContinuousLinearMap.restrictScalarsL ℂ (Fin D → ℂ) ℂ ℝ ℝ) (fderiv ℂ H z)))
      ((ContinuousLinearMap.compL ℝ (Fin D → ℂ) ℂ ℝ Complex.reCLM).comp
        ((ContinuousLinearMap.restrictScalarsL ℂ (Fin D → ℂ) ℂ ℝ ℝ).comp
          ((fderiv ℂ (fderiv ℂ H) y).restrictScalars ℝ))) y :=
    (ContinuousLinearMap.compL ℝ (Fin D → ℂ) ℂ ℝ Complex.reCLM).hasFDerivAt.comp y
    ((ContinuousLinearMap.restrictScalarsL ℂ (Fin D → ℂ) ℂ ℝ ℝ).hasFDerivAt.comp y hD)
  have hv : ∀ v w : Fin D → ℂ, fderiv ℝ (fderiv ℝ fun z => (H z).re) y v w =
      (fderiv ℂ (fderiv ℂ H) y v w).re := by
    intro v w
    rw [h1.fderiv_eq, h2.fderiv]
    first
      | rfl
      | simp
  ext i k
  simp only [hessC, hv, Matrix.zero_apply, map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
  simp [Complex.mul_re, Complex.mul_im]

theorem st_maDens_cons_congr {n : ℕ} {f g : (Fin (n + 1) → ℂ) → ℝ}
    (φ : Fin n → (Fin (n + 1) → ℂ) → ℝ) {y : Fin (n + 1) → ℂ} (h : f =ᶠ[𝓝 y] g) :
    maDens (Fin.cons f φ) y = maDens (Fin.cons g φ) y := by
  apply maDens_congr_of_hessC_eq
  intro k
  refine Fin.cases ?_ (fun i => ?_) k
  · simpa only [Fin.cons_zero] using st_hessC_congr h
  · simp only [Fin.cons_succ]

private lemma continuous_of_atlas_smooth' (A : FinHolAtlas e X) {f : X → ℝ} (hf : A.Smooth f) :
    Continuous f := by
  rw [continuous_iff_continuousAt]
  intro x
  obtain ⟨k, hk⟩ := A.cover x
  have hs : (A.chart k).target ∩ (A.chart k).symm ⁻¹' univ ∈ 𝓝 ((A.chart k) x) := by
    rw [preimage_univ, inter_univ]
    exact (A.chart k).open_target.mem_nhds ((A.chart k).map_source hk)
  have h1 : ContinuousAt (f ∘ (A.chart k).symm) ((A.chart k) x) :=
    (hf k).continuousOn.continuousAt hs
  have h2 : ContinuousAt ((f ∘ (A.chart k).symm) ∘ (A.chart k)) x :=
    ContinuousAt.comp (f := A.chart k) h1 ((A.chart k).continuousAt hk)
  refine h2.congr ?_
  filter_upwards [(A.chart k).open_source.mem_nhds hk] with z hz
  simp [(A.chart k).left_inv hz]

theorem st_mInt_eq_chart [CompactSpace X] [T2Space X] (A : FinHolAtlas e X)
    (Ψ : Fin e → LocPot X) (hΨ : ∀ i, IsPotential A (Ψ i)) (j : Fin A.n) (g : X → ℝ)
    (hg : Continuous g) (hgs : tsupport g ⊆ (A.chart j).source) :
    mInt A Ψ g = ∫ y in (A.chart j).target, g ((A.chart j).symm y) * locDens A Ψ j y := by
  unfold mInt
  rw [dif_pos (existsPartition A)]
  exact mIntLocalize A _ Ψ hΨ j g hgs (mIntegrableCont A Ψ hΨ g hg)

theorem st_mInt_eq_piece [CompactSpace X] [T2Space X] (A : FinHolAtlas e X)
    (Ψ : Fin e → LocPot X) (hΨ : ∀ i, IsPotential A (Ψ i)) (j : Fin A.n) (G : Set X)
    (hG : G ⊆ (A.chart j).source) (g : X → ℝ) (hg : Continuous g) (hgs : tsupport g ⊆ G) :
    mInt A Ψ g = ∫ y in (A.chart j).target ∩ (A.chart j).symm ⁻¹' G,
      g ((A.chart j).symm y) * locDens A Ψ j y := by
  rw [st_mInt_eq_chart A Ψ hΨ j g hg (hgs.trans hG)]
  refine setIntegral_eq_of_subset_of_forall_diff_eq_zero (A.chart j).open_target.measurableSet
    inter_subset_left ?_
  intro y hy
  have hyG : (A.chart j).symm y ∉ G := fun h' => hy.2 ⟨hy.1, h'⟩
  have hg0 : g ((A.chart j).symm y) = 0 := image_eq_zero_of_notMem_tsupport (fun h' => hyG (hgs h'))
  rw [hg0, zero_mul]

section Piece

variable [CompactSpace X] [T2Space X] (A : FinHolAtlas (e + 1) X) (Φ : Fin e → LocPot X)
  (hΦ : ∀ i, IsPotential A (Φ i)) (j : Fin A.n) (G : Set X) (hGo : IsOpen G)
  (hG : G ⊆ (A.chart j).source) (x0 : Fin e → X) (hGU : ∀ i, G ⊆ (Φ i).U (x0 i))

include hΦ hG hGU in

theorem st_locDens_piece (u : X → ℝ) (hu : A.Smooth u) {y : Fin (e + 1) → ℂ}
    (hy : y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' G) :
    locDens A (Fin.cons (LocPot.ofFun u) Φ) j y =
      maDens (Fin.cons (u ∘ (A.chart j).symm) fun i => (Φ i).φ (x0 i) ∘ (A.chart j).symm) y := by
  unfold locDens
  apply maDens_congr_of_hessC_eq
  intro k
  refine Fin.cases ?_ (fun i => ?_) k
  · first
      | rfl
      | (simp only [Fin.cons_zero]; rfl)
      | simp [LocPot.ofFun, Function.comp_def]
  · simp only [Fin.cons_succ]
    have hyG : (A.chart j).symm y ∈ G := hy.2
    obtain ⟨W, hWo, haW, Gh, hGh, hdiff⟩ :=
      (hΦ i).2 ((A.chart j).symm y) (x0 i) ((A.chart j).symm y) ⟨(Φ i).mem_U _, hGU i hyG⟩
    have hSo : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹'
        (W ∩ (Φ i).U ((A.chart j).symm y) ∩ (Φ i).U (x0 i))) :=
      (A.chart j).isOpen_inter_preimage_symm ((hWo.inter ((Φ i).isOpen_U _)).inter ((Φ i).isOpen_U _))
    have hyS : y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹'
        (W ∩ (Φ i).U ((A.chart j).symm y) ∩ (Φ i).U (x0 i)) :=
      ⟨hy.1, ⟨⟨haW, (Φ i).mem_U _⟩, hGU i hyG⟩⟩
    have hSn := hSo.mem_nhds hyS
    have hf2 : ∀ᶠ z in 𝓝 y, ContDiffAt ℝ 2 ((Φ i).φ (x0 i) ∘ (A.chart j).symm) z := by
      filter_upwards [hSn] with z hz
      have hon := (hΦ i).1 (x0 i) j
      exact ((hon.mono (fun w hw => ⟨hw.1, hw.2.2⟩)).contDiffAt (hSo.mem_nhds hz)).of_le
        two_le_infty_withTop
    have hK : ∀ z ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹'
        (W ∩ (Φ i).U ((A.chart j).symm y) ∩ (Φ i).U (x0 i)),
        AnalyticAt ℂ (Gh ∘ (A.chart j).symm) z := fun z hz => hGh j z ⟨hz.1, hz.2.1.1⟩
    have hh : ∀ᶠ z in 𝓝 y, ContDiffAt ℝ 2 (fun w => ((Gh ∘ (A.chart j).symm) w).re) z := by
      filter_upwards [hSn] with z hz
      exact contDiffAt_two_re_of_analyticAt (hK z hz)
    have heq : (fun y' => (Φ i).φ ((A.chart j).symm y) ((A.chart j).symm y')) =ᶠ[𝓝 y]
        fun w => ((Φ i).φ (x0 i) ∘ (A.chart j).symm) w + ((Gh ∘ (A.chart j).symm) w).re := by
      filter_upwards [hSn] with z hz
      have hz' := hdiff ((A.chart j).symm z) hz.2
      simp only [Function.comp_apply]
      linarith
    rw [st_hessC_congr heq, hessC_add_potential hf2 hh, hessC_re_of_analyticAt (hK y hyS), add_zero]

include hΦ hGo hG hGU in

theorem st_left_piece (w ψ : X → ℝ) (hw : A.Smooth w) (hψ : A.Smooth ψ) (hψG : tsupport ψ ⊆ G) :
    mInt A (Fin.cons (LocPot.ofFun w) Φ) ψ =
      ∫ y in (A.chart j).target ∩ (A.chart j).symm ⁻¹' G,
        (A.chart j).target.indicator (ψ ∘ (A.chart j).symm) y *
          maDens (Fin.cons (w ∘ (A.chart j).symm)
            fun i => (Φ i).φ (x0 i) ∘ (A.chart j).symm) y := by
  have hP0 : IsPotential A (LocPot.ofFun w) := by
    unfold IsPotential
    refine ⟨fun _ => hw, fun x x' z _ => ⟨univ, isOpen_univ, mem_univ _, fun _ => 0, ?_, ?_⟩⟩
    · intro k z' _
      exact analyticAt_const
    · intro z' _
      simp [LocPot.ofFun]
  have hΨ : ∀ i, IsPotential A ((Fin.cons (LocPot.ofFun w) Φ : Fin (e + 1) → LocPot X) i) := by
    intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · simpa only [Fin.cons_zero] using hP0
    · simpa only [Fin.cons_succ] using hΦ i
  rw [st_mInt_eq_piece A _ hΨ j G hG ψ (continuous_of_atlas_smooth' A hψ) hψG]
  have hSm : MeasurableSet ((A.chart j).target ∩ (A.chart j).symm ⁻¹' G) :=
    ((A.chart j).isOpen_inter_preimage_symm hGo).measurableSet
  refine setIntegral_congr_fun hSm ?_
  intro y hy
  have h1 := st_locDens_piece A Φ hΦ j G hG x0 hGU w hw hy
  have h2 : (A.chart j).target.indicator (ψ ∘ (A.chart j).symm) y = ψ ((A.chart j).symm y) :=
    Set.indicator_of_mem hy.1 _
  simp only [h1, h2]

include hΦ hGo hG hGU in

theorem st_right_piece (w ψ : X → ℝ) (hw : A.Smooth w) (hψ : A.Smooth ψ) (hψG : tsupport ψ ⊆ G) :
    mInt A (Fin.cons (LocPot.ofFun ψ) Φ) w =
      ∫ y in (A.chart j).target ∩ (A.chart j).symm ⁻¹' G,
        (w ∘ (A.chart j).symm) y *
          maDens (Fin.cons ((A.chart j).target.indicator (ψ ∘ (A.chart j).symm))
            fun i => (Φ i).φ (x0 i) ∘ (A.chart j).symm) y := by
  obtain ⟨ρ, hρs, hρ1, -⟩ := exists_tsupport_one_of_isOpen_isClosed hGo
    isClosed_closure.isCompact (isClosed_tsupport ψ) hψG
  have hpot := st_isPotential_cons A hψ hΦ

  have h1 : mInt A (Fin.cons (LocPot.ofFun ψ) Φ) w =
      mInt A (Fin.cons (LocPot.ofFun ψ) Φ) (fun x => ρ x * w x) := by
    unfold mInt
    split_ifs with hP
    · unfold integralWith
      refine Finset.sum_congr rfl fun k _ => ?_
      refine setIntegral_congr_fun (A.chart k).open_target.measurableSet ?_
      intro y hy
      by_cases hs : (A.chart k).symm y ∈ tsupport ψ
      · simp [hρ1 hs]
      · simp [st_locDens_cons_eq_zero A k ψ Φ hy hs]
    · rfl
  rw [h1, st_mInt_eq_piece A _ hpot j G hG (fun x => ρ x * w x) (ρ.continuous.mul (st_smooth_continuous A hw))
    ((tsupport_mul_subset_left).trans hρs)]
  refine setIntegral_congr_fun ((A.chart j).isOpen_inter_preimage_symm hGo).measurableSet ?_
  intro y hy
  have hV : (A.chart j).target ∩ (A.chart j).symm ⁻¹' G ∈ 𝓝 y :=
    ((A.chart j).isOpen_inter_preimage_symm hGo).mem_nhds hy
  have hev : ψ ∘ (A.chart j).symm =ᶠ[𝓝 y] (A.chart j).target.indicator (ψ ∘ (A.chart j).symm) := by
    filter_upwards [hV] with z hz
    rw [indicator_of_mem hz.1]
  simp only
  rw [st_locDens_piece A Φ hΦ j G hG x0 hGU ψ hψ hy, ← st_maDens_cons_congr _ hev]
  by_cases hs : (A.chart j).symm y ∈ tsupport ψ
  · simp [hρ1 hs]
  · have h0 := st_locDens_cons_eq_zero A j ψ Φ hy.1 hs
    rw [st_locDens_piece A Φ hΦ j G hG x0 hGU ψ hψ hy] at h0
    simp [h0]

include hΦ hGo hG hGU in

theorem st_symm_piece (hP : ReciprocityTheory.AnForm.A.PartsStatement) (w ψ : X → ℝ) (hw : A.Smooth w)
    (hψ : A.Smooth ψ) (hψG : tsupport ψ ⊆ G) :
    mInt A (Fin.cons (LocPot.ofFun w) Φ) ψ = mInt A (Fin.cons (LocPot.ofFun ψ) Φ) w := by
  rw [st_left_piece A Φ hΦ j G hGo hG x0 hGU w ψ hw hψ hψG,
    st_right_piece A Φ hΦ j G hGo hG x0 hGU w ψ hw hψ hψG]
  have hSo : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' G) :=
    (A.chart j).isOpen_inter_preimage_symm hGo
  have hsG : tsupport ψ ⊆ (A.chart j).source := hψG.trans hG
  have hKc : IsCompact ((A.chart j) '' tsupport ψ) :=
    (isClosed_tsupport ψ).isCompact.image_of_continuousOn ((A.chart j).continuousOn.mono hsG)
  have hsupp : Function.support ((A.chart j).target.indicator (ψ ∘ (A.chart j).symm)) ⊆
      (A.chart j) '' tsupport ψ := by
    intro y hy
    have hy' := Function.mem_support.1 hy
    by_cases hyt : y ∈ (A.chart j).target
    · refine ⟨(A.chart j).symm y, subset_tsupport _ ?_, (A.chart j).right_inv hyt⟩
      rw [Set.indicator_of_mem hyt] at hy'
      exact hy'
    · exact absurd (Set.indicator_of_notMem hyt _) hy'
  have hts : tsupport ((A.chart j).target.indicator (ψ ∘ (A.chart j).symm)) ⊆
      (A.chart j) '' tsupport ψ := closure_minimal hsupp hKc.isClosed
  have hKS : (A.chart j) '' tsupport ψ ⊆ (A.chart j).target ∩ (A.chart j).symm ⁻¹' G := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨(A.chart j).map_source (hsG hx), ?_⟩
    show (A.chart j).symm ((A.chart j) x) ∈ G
    rw [(A.chart j).left_inv (hsG hx)]
    exact hψG hx
  have hH : ReciprocityTheory.AnForm.A.PartsHyp (fun i => (Φ i).φ (x0 i) ∘ (A.chart j).symm)
      ((A.chart j).target.indicator (ψ ∘ (A.chart j).symm)) (w ∘ (A.chart j).symm)
      ((A.chart j).target ∩ (A.chart j).symm ⁻¹' G) := by
    unfold ReciprocityTheory.AnForm.A.PartsHyp
    refine ⟨hSo, ?_, hKc.of_isClosed_subset (isClosed_tsupport _) hts, hts.trans hKS, ?_, ?_⟩
    · exact (((hψ j).mono (fun y hy => ⟨hy.1, mem_univ _⟩)).of_le three_le_infty_withTop).congr
        (fun y hy => Set.indicator_of_mem hy.1 _)
    · exact ((hw j).mono (fun y hy => ⟨hy.1, mem_univ _⟩)).of_le three_le_infty_withTop
    · intro i
      exact (((hΦ i).1 (x0 i) j).mono (fun y hy => ⟨hy.1, hGU i hy.2⟩)).of_le three_le_infty_withTop
  have key := (hP e (fun i => (Φ i).φ (x0 i) ∘ (A.chart j).symm)
    ((A.chart j).target.indicator (ψ ∘ (A.chart j).symm)) (w ∘ (A.chart j).symm)
    ((A.chart j).target ∩ (A.chart j).symm ⁻¹' G) hH).2.2.2.2
  exact key.symm

end Piece

theorem st_byPartsSymm_of (hP : ReciprocityTheory.AnForm.A.PartsStatement) : ByPartsSymmStatement := by
  intro e X _ _ _ A v w hv hw Φ hΦ
  obtain ⟨M, θ, G, j, x0, hθs, -, hθ1, hθG, hGo, hGs, hGU⟩ := st_exists_good_partition A Φ
  have hsum : (fun x => ∑ m, θ m x * v x) = v := by
    funext x
    rw [← Finset.sum_mul, hθ1, one_mul]
  have hL := st_mInt_finset_sum A _ (st_isPotential_cons A hw hΦ) Finset.univ
    (fun m x => θ m x * v x) (fun m => st_smooth_continuous A (st_smooth_mul A (hθs m) hv))
  have hR := st_mInt_cons_finset_sum A Φ hΦ Finset.univ (fun m x => θ m x * v x)
    (fun m => st_smooth_mul A (hθs m) hv) w (st_smooth_continuous A hw)
  rw [hsum] at hL hR
  rw [hL, hR]
  refine Finset.sum_congr rfl fun m _ => ?_
  exact st_symm_piece A Φ hΦ (j m) (G m) (hGo m) (hGs m) (x0 m) (hGU m) hP w _ hw
    (st_smooth_mul A (hθs m) hv) ((tsupport_mul_subset_left).trans (hθG m))

end

end ReciprocityTheory.AnForm.M
