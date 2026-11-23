import Mathlib
import ReciprocityTheory.AnalyticForms.PotentialTheory.Stokes
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.FourB.CompactSupportStokes

open MeasureTheory Filter Topology Set ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M FinHolAtlas
open scoped ContDiff Manifold

variable {e : ℕ} {X : Type} [TopologicalSpace X]

theorem chi_contOn (A : FinHolAtlas e X) (χ : ChartPartition A) (k j : Fin A.n) :
    ContinuousOn (fun y => χ.χ k ((A.chart j).symm y)) (A.chart j).target := by
  have := (χ.smooth k j).continuousOn
  simpa [Function.comp_def] using this

theorem integrableOn_target (A : FinHolAtlas e X) (k : Fin A.n) {F : (Fin e → ℂ) → ℝ}
    (hF : ContinuousOn F (A.chart k).target) {S : Set X} (hS : IsCompact S)
    (hSk : S ⊆ (A.chart k).source)
    (hz : ∀ y ∈ (A.chart k).target, (A.chart k).symm y ∉ S → F y = 0) :
    IntegrableOn F (A.chart k).target := by
  have hC : IsCompact ((A.chart k) '' S) :=
    hS.image_of_continuousOn ((A.chart k).continuousOn.mono hSk)
  have hCt : (A.chart k) '' S ⊆ (A.chart k).target := by
    rintro _ ⟨x, hx, rfl⟩; exact (A.chart k).map_source (hSk hx)
  refine ((hF.mono hCt).integrableOn_compact hC).of_forall_sdiff_eq_zero
    (A.chart k).open_target.measurableSet ?_
  rintro y ⟨hy, hyC⟩
  exact hz y hy fun h => hyC ⟨_, h, (A.chart k).right_inv hy⟩

theorem locDens_cons_congr (A : FinHolAtlas (e + 1) X) {P Q : LocPot X} (Φ : Fin e → LocPot X)
    (h : P.φ = Q.φ) (k : Fin A.n) (y : Fin (e + 1) → ℂ) :
    locDens A (Fin.cons P Φ) k y = locDens A (Fin.cons Q Φ) k y := by
  rw [locDens_cons, locDens_cons, h]

theorem chartMove (A : FinHolAtlas e X) (χ : ChartPartition A) (Φ : Fin e → LocPot X)
    (hΦ : ∀ i, IsPotential A (Φ i)) (j k : Fin A.n) (g : X → ℝ)
    (hs : ∀ y ∈ (A.chart k).target, (A.chart k).symm y ∉ (A.chart j).source →
      g ((A.chart k).symm y) * locDens A Φ k y = 0) :
    ∫ y in (A.chart k).target,
        χ.χ k ((A.chart k).symm y) * g ((A.chart k).symm y) * locDens A Φ k y =
      ∫ y in (A.chart j).target,
        χ.χ k ((A.chart j).symm y) * g ((A.chart j).symm y) * locDens A Φ j y := by
  have hU : IsOpen ((A.chart k).target ∩ (A.chart k).symm ⁻¹' (A.chart j).source) :=
    (A.chart k).continuousOn_symm.isOpen_inter_preimage (A.chart k).open_target
      (A.chart j).open_source
  have hτ : AnalyticOnNhd ℂ (A.chart j ∘ (A.chart k).symm)
      ((A.chart k).target ∩ (A.chart k).symm ⁻¹' (A.chart j).source) := A.holo k j
  have hinj : Set.InjOn (A.chart j ∘ (A.chart k).symm)
      ((A.chart k).target ∩ (A.chart k).symm ⁻¹' (A.chart j).source) := by
    intro a ha b hb hab
    exact (A.chart k).symm.injOn ha.1 hb.1 ((A.chart j).injOn ha.2 hb.2 hab)
  have himg : (A.chart j ∘ (A.chart k).symm) ''
      ((A.chart k).target ∩ (A.chart k).symm ⁻¹' (A.chart j).source) ⊆ (A.chart j).target := by
    rintro _ ⟨z, hz, rfl⟩; exact (A.chart j).map_source hz.2
  have hin : ∀ w ∈ (A.chart j).target, (A.chart j).symm w ∈ (A.chart k).source →
      w ∈ (A.chart j ∘ (A.chart k).symm) ''
        ((A.chart k).target ∩ (A.chart k).symm ⁻¹' (A.chart j).source) := by
    intro w hw h2
    refine ⟨A.chart k ((A.chart j).symm w), ⟨(A.chart k).map_source h2, ?_⟩, ?_⟩
    · show (A.chart k).symm (A.chart k ((A.chart j).symm w)) ∈ (A.chart j).source
      rw [(A.chart k).left_inv h2]; exact (A.chart j).map_target hw
    · show A.chart j ((A.chart k).symm (A.chart k ((A.chart j).symm w))) = w
      rw [(A.chart k).left_inv h2, (A.chart j).right_inv hw]
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (A.chart k).open_target.measurableSet
      Set.inter_subset_left ?z1,
    setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (A.chart j).open_target.measurableSet
      himg ?z2,
    ReciprocityTheory.AnForm.A.integral_image_eq_integral_normSq_det_smul _ _ hU hτ hinj]
  · refine setIntegral_congr_fun hU.measurableSet (fun z hz => ?_)
    have hz2 : (A.chart k).symm z ∈ (A.chart j).source := hz.2
    simp only [Function.comp_apply, smul_eq_mul, (A.chart j).left_inv hz2]
    rw [ReciprocityTheory.AnForm.A.det_jacC, Complex.normSq_eq_norm_sq,
      locDensChart A Φ hΦ k j z hz.1 hz2]
    ring
  case z1 =>
    rintro y ⟨hy, hyU⟩
    have h1 : (A.chart k).symm y ∉ (A.chart j).source := fun h => hyU ⟨hy, h⟩
    rw [mul_assoc, hs y hy h1, mul_zero]
  case z2 =>
    rintro w ⟨hw, hwU⟩
    have h1 : (A.chart j).symm w ∉ (A.chart k).source := fun h => hwU (hin w hw h)
    have h2 : (A.chart j).symm w ∉ tsupport (χ.χ k) := fun h => h1 (χ.tsupport_subset k h)
    simp only [image_eq_zero_of_notMem_tsupport h2, zero_mul]

theorem localize (A : FinHolAtlas e X) (χ : ChartPartition A) (Φ : Fin e → LocPot X)
    (hΦ : ∀ i, IsPotential A (Φ i)) (j : Fin A.n) (g : X → ℝ)
    (hs : ∀ k, ∀ y ∈ (A.chart k).target, (A.chart k).symm y ∉ (A.chart j).source →
      g ((A.chart k).symm y) * locDens A Φ k y = 0)
    (hint : ∀ k, IntegrableOn (fun y => χ.χ k ((A.chart j).symm y) * g ((A.chart j).symm y) *
      locDens A Φ j y) (A.chart j).target) :
    integralWith A χ Φ g =
      ∫ y in (A.chart j).target, g ((A.chart j).symm y) * locDens A Φ j y := by
  unfold integralWith
  rw [Finset.sum_congr rfl (fun k _ => chartMove A χ Φ hΦ j k g (hs k)),
    ← integral_finsetSum _ (fun k _ => hint k)]
  refine setIntegral_congr_fun (A.chart j).open_target.measurableSet (fun y _ => ?_)
  rw [← Finset.sum_mul, ← Finset.sum_mul, χ.sum_eq_one, one_mul]

theorem integrableOn_term (A : FinHolAtlas (e + 1) X) (χ : ChartPartition A)
    (Φ : Fin e → LocPot X) (hΦ : ∀ i, IsPotential A (Φ i)) (k j : Fin A.n) (w : X → ℝ)
    (hw : A.Smooth w) {L : Set X} (hL : IsCompact L) (hwL : tsupport w ⊆ L)
    (hLj : k = j ∨ L ⊆ (A.chart j).source) :
    IntegrableOn (fun y => χ.χ k ((A.chart j).symm y) * 1 *
      locDens A (Fin.cons (LocPot.ofFun w) Φ) j y) (A.chart j).target := by
  have hF : ContinuousOn (fun y => χ.χ k ((A.chart j).symm y) * 1 *
      locDens A (Fin.cons (LocPot.ofFun w) Φ) j y) (A.chart j).target :=
    ((chi_contOn A χ k j).mul continuousOn_const).mul
      (locDensCont A _ (st_isPotential_cons A hw hΦ) j)
  rcases hLj with rfl | hLj
  · refine integrableOn_target A k hF (hL.inter_left (isClosed_tsupport (χ.χ k)))
      (inter_subset_left.trans (χ.tsupport_subset k)) ?_
    intro y hy hyS
    by_cases h1 : (A.chart k).symm y ∈ tsupport (χ.χ k)
    · have h2 : (A.chart k).symm y ∉ tsupport w := fun h => hyS ⟨h1, hwL h⟩
      rw [st_locDens_cons_eq_zero A k w Φ hy h2, mul_zero]
    · rw [image_eq_zero_of_notMem_tsupport h1, zero_mul, zero_mul]
  · refine integrableOn_target A j hF hL hLj ?_
    intro y hy hyL
    rw [st_locDens_cons_eq_zero A j w Φ hy (fun h => hyL (hwL h)), mul_zero]

theorem integralWith_cons_sum [T2Space X] (A : FinHolAtlas (e + 1) X) (χ : ChartPartition A)
    (Φ : Fin e → LocPot X) (hΦ : ∀ i, IsPotential A (Φ i)) {ι : Type*} (s : Finset ι)
    (f : ι → X → ℝ) (hf : ∀ m, A.Smooth (f m)) {L : Set X} (hL : IsCompact L)
    (hfL : ∀ m, tsupport (f m) ⊆ L) :
    integralWith A χ (Fin.cons (LocPot.ofFun fun x => ∑ m ∈ s, f m x) Φ) (fun _ => 1) =
      ∑ m ∈ s, integralWith A χ (Fin.cons (LocPot.ofFun (f m)) Φ) (fun _ => 1) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty]
    unfold integralWith
    refine Finset.sum_eq_zero fun k _ => ?_
    refine setIntegral_eq_zero_of_forall_eq_zero fun y hy => ?_
    have h0 : (A.chart k).symm y ∉ tsupport (fun x => ∑ m ∈ (∅ : Finset ι), f m x) := by
      simp
    rw [st_locDens_cons_eq_zero A k _ Φ hy h0, mul_zero]
  | insert a s ha ih =>
    have hS : A.Smooth (fun x => ∑ m ∈ s, f m x) := st_smooth_sum A s hf
    have hSL : tsupport (fun x => ∑ m ∈ s, f m x) ⊆ L := by
      refine closure_minimal ?_ hL.isClosed
      intro x hx
      obtain ⟨m, -, hm⟩ := Finset.exists_ne_zero_of_sum_ne_zero hx
      exact hfL m (subset_tsupport _ hm)
    have hd : ∀ k, ∀ y ∈ (A.chart k).target,
        locDens A (Fin.cons (LocPot.ofFun fun x => ∑ m ∈ insert a s, f m x) Φ) k y =
          locDens A (Fin.cons (LocPot.ofFun (f a)) Φ) k y +
            locDens A (Fin.cons (LocPot.ofFun fun x => ∑ m ∈ s, f m x) Φ) k y := by
      intro k y hy
      rw [← locDens_cons_add A _ _ Φ (isPotential_ofFun A _ (hf a)) (isPotential_ofFun A _ hS) k hy]
      refine locDens_cons_congr A Φ ?_ k y
      funext x z
      simp [Finset.sum_insert ha, LocPot.ofFun]
      rfl
    rw [Finset.sum_insert ha, ← ih]
    unfold integralWith
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← integral_add (integrableOn_term A χ Φ hΦ k k _ (hf a) hL (hfL a) (Or.inl rfl))
      (integrableOn_term A χ Φ hΦ k k _ hS hL hSL (Or.inl rfl))]
    refine setIntegral_congr_fun (A.chart k).open_target.measurableSet fun y hy => ?_
    simp only
    rw [hd k y hy]
    ring

theorem piece_eq_zero [T2Space X] (A : FinHolAtlas (e + 1) X) (χ : ChartPartition A)
    (Φ : Fin e → LocPot X) (hΦ : ∀ i, IsPotential A (Φ i)) (j : Fin A.n) (G : Set X)
    (hGo : IsOpen G) (hG : G ⊆ (A.chart j).source) (x0 : Fin e → X)
    (hGU : ∀ i, G ⊆ (Φ i).U (x0 i)) (w : X → ℝ) (hw : A.Smooth w)
    (hwc : IsCompact (tsupport w)) (hwG : tsupport w ⊆ G) :
    integralWith A χ (Fin.cons (LocPot.ofFun w) Φ) (fun _ => 1) = 0 := by
  have hpot := st_isPotential_cons A hw hΦ
  rw [localize A χ _ hpot j (fun _ => 1) ?hs ?hint]
  case hs =>
    intro k y hy hyj
    rw [st_locDens_cons_eq_zero A k w Φ hy (fun h => hyj (hG (hwG h))), mul_zero]
  case hint =>
    intro k
    exact integrableOn_term A χ Φ hΦ k j w hw hwc subset_rfl (Or.inr (hwG.trans hG))
  set T := (A.chart j).target with hT
  set s := (A.chart j).symm with hs
  set V := T ∩ s ⁻¹' G with hVdef
  have hVo : IsOpen V := (A.chart j).isOpen_inter_preimage_symm hGo
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (A.chart j).open_target.measurableSet
    (inter_subset_left : V ⊆ T) ?hz]
  case hz =>
    rintro y ⟨hy, hyV⟩
    have : s y ∉ tsupport w := fun h => hyV ⟨hy, hwG h⟩
    rw [st_locDens_cons_eq_zero A j w Φ hy this, mul_zero]
  set φh : Fin e → (Fin (e + 1) → ℂ) → ℝ := fun i => (Φ i).φ (x0 i) ∘ s with hφh
  set v : (Fin (e + 1) → ℂ) → ℝ := T.indicator (w ∘ s) with hv
  have hloc : ∀ y ∈ V, (fun _ : X => (1 : ℝ)) (s y) * locDens A (Fin.cons (LocPot.ofFun w) Φ) j y =
      maDens (Fin.cons v φh) y := by
    intro y hy
    have hb := locDensBase A (Fin.cons (LocPot.ofFun w) Φ) hpot j y hy.1 (Fin.cons (s y) x0) (by
      intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · simp [LocPot.ofFun]
      · simpa using hGU i hy.2)
    rw [one_mul, hb]
    have hev : w ∘ s =ᶠ[𝓝 y] v := by
      filter_upwards [(A.chart j).open_target.mem_nhds hy.1] with z hz
      exact (indicator_of_mem (s := T) hz _).symm
    rw [← st_maDens_cons_congr φh hev]
    congr 1
    funext i y'
    refine Fin.cases ?_ (fun i => ?_) i
    · simp [LocPot.ofFun, hs]
    · simp [hφh, hs]
  rw [setIntegral_congr_fun hVo.measurableSet hloc]
  have hVT : V ⊆ T ∩ s ⁻¹' univ := fun y hy => ⟨hy.1, mem_univ _⟩
  have hCc : IsCompact ((A.chart j) '' tsupport w) :=
    hwc.image_of_continuousOn ((A.chart j).continuousOn.mono (hwG.trans hG))
  have hCV : (A.chart j) '' tsupport w ⊆ V := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨(A.chart j).map_source (hG (hwG hx)), ?_⟩
    show s (A.chart j x) ∈ G
    rw [hs, (A.chart j).left_inv (hG (hwG hx))]
    exact hwG hx
  have hsupp : tsupport v ⊆ (A.chart j) '' tsupport w := by
    refine closure_minimal ?_ hCc.isClosed
    intro y hy
    have hyT : y ∈ T := by
      by_contra h
      exact hy (indicator_of_notMem h _)
    rw [Function.mem_support, hv, indicator_of_mem hyT] at hy
    exact ⟨s y, subset_tsupport _ hy, (A.chart j).right_inv hyT⟩
  have h3 : ∀ {f : X → ℝ}, A.Smooth f → ContDiffOn ℝ 3 (f ∘ s) V := fun hf =>
    ((hf j).of_le (by norm_cast)).mono hVT
  exact ReciprocityTheory.AnForm.A.massZero_thm e φh v V ⟨hVo,
    (h3 hw).congr fun y hy => indicator_of_mem hy.1 _,
    HasCompactSupport.intro' hCc hCc.isClosed (fun y hy => image_eq_zero_of_notMem_tsupport
      fun h => hy (hsupp h)),
    hsupp.trans hCV, contDiffOn_const, fun i => (((hΦ i).1 (x0 i) j).of_le (by norm_cast)).mono
      fun y hy => ⟨hy.1, hGU i hy.2⟩⟩

theorem stokes_chart [T2Space X] (A : FinHolAtlas (e + 1) X) (χ : ChartPartition A)
    (Φ : Fin e → LocPot X) (hΦ : ∀ i, IsPotential A (Φ i)) (j : Fin A.n) (w : X → ℝ)
    (hw : A.Smooth w) (hwc : IsCompact (tsupport w)) (hwj : tsupport w ⊆ (A.chart j).source) :
    integralWith A χ (Fin.cons (LocPot.ofFun w) Φ) (fun _ => 1) = 0 := by
  classical
  have hCc : IsCompact ((A.chart j) '' tsupport w) :=
    hwc.image_of_continuousOn ((A.chart j).continuousOn.mono hwj)
  have hCt : (A.chart j) '' tsupport w ⊆ (A.chart j).target := by
    rintro _ ⟨x, hx, rfl⟩; exact (A.chart j).map_source (hwj hx)

  obtain ⟨O, hO⟩ : ∃ O : (Fin (e + 1) → ℂ) → Set (Fin (e + 1) → ℂ), ∀ p,
      O p = (A.chart j).target ∩ (A.chart j).symm ⁻¹' ⋂ i, (Φ i).U ((A.chart j).symm p) :=
    ⟨_, fun _ => rfl⟩
  have hOo : ∀ p, IsOpen (O p) := fun p => by
    rw [hO]
    exact (A.chart j).isOpen_inter_preimage_symm (isOpen_iInter_of_finite fun i => (Φ i).isOpen_U _)
  have hpO : ∀ p ∈ (A.chart j) '' tsupport w, O p ∈ 𝓝 p := fun p hp => by
    refine (hOo p).mem_nhds ?_
    rw [hO]
    exact ⟨hCt hp, mem_iInter.2 fun i => (Φ i).mem_U _⟩
  obtain ⟨t, -, hcov⟩ := hCc.elim_nhds_subcover O hpO
  obtain ⟨β, hβ⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, Fin (e + 1) → ℂ)
    hCc.isClosed (fun p : t => O p.1) (fun p => hOo p.1) (by
      intro y hy
      obtain ⟨p, hp, hyp⟩ := mem_iUnion₂.1 (hcov hy)
      exact mem_iUnion.2 ⟨⟨p, hp⟩, hyp⟩)
  have hβs : ∀ p, ContDiff ℝ ∞ (β p) := fun p => contMDiff_iff_contDiff.1 (β p).contMDiff

  obtain ⟨wp, hwp⟩ : ∃ wp : t → X → ℝ, ∀ p x, wp p x = β p (A.chart j x) * w x :=
    ⟨_, fun _ _ => rfl⟩
  have hsum : (fun x => ∑ p, wp p x) = w := by
    funext x
    simp only [hwp]
    rw [← Finset.sum_mul]
    by_cases hx : x ∈ tsupport w
    · have h1 : ∑ p, β p (A.chart j x) = 1 := by
        rw [← finsum_eq_sum_of_fintype]
        exact β.sum_eq_one ⟨x, hx, rfl⟩
      rw [h1, one_mul]
    · rw [image_eq_zero_of_notMem_tsupport hx, mul_zero]
  have hwps : ∀ p, A.Smooth (wp p) := by
    intro p k
    apply contDiffOn_of_locally_contDiffOn
    rintro y ⟨hy, -⟩
    by_cases hyj : (A.chart k).symm y ∈ (A.chart j).source
    · refine ⟨(A.chart k).target ∩ (A.chart k).symm ⁻¹' (A.chart j).source,
        (A.chart k).isOpen_inter_preimage_symm (A.chart j).open_source, ⟨hy, hyj⟩, ?_⟩
      have h1 : ContDiffOn ℝ ∞ ((β p) ∘ (A.chart j ∘ (A.chart k).symm))
          ((A.chart k).target ∩ (A.chart k).symm ⁻¹' (A.chart j).source) :=
        (hβs p).comp_contDiffOn (st_trans_smooth A k j)
      refine ((h1.mono fun z hz => hz.2).mul ((hw k).mono fun z hz => hz.1)).congr ?_
      intro z _
      simp only [Function.comp_apply, hwp]
    · have hyw : (A.chart k).symm y ∉ tsupport w := fun h => hyj (hwj h)
      refine ⟨(A.chart k).target ∩ (A.chart k).symm ⁻¹' (tsupport w)ᶜ,
        (A.chart k).isOpen_inter_preimage_symm (isClosed_tsupport w).isOpen_compl, ⟨hy, hyw⟩, ?_⟩
      refine (contDiffOn_const (c := (0 : ℝ))).congr ?_
      intro z hz
      simp only [Function.comp_apply, hwp]
      rw [image_eq_zero_of_notMem_tsupport hz.2.2, mul_zero]
  have hwpw : ∀ p, tsupport (wp p) ⊆ tsupport w := fun p => by
    refine closure_minimal ?_ (isClosed_tsupport w)
    intro x hx
    rw [Function.mem_support, hwp] at hx
    exact subset_tsupport _ (right_ne_zero_of_mul hx)
  have hwpG : ∀ p : t, tsupport (wp p) ⊆ (A.chart j).source ∩ (A.chart j) ⁻¹' O p.1 := by
    intro p
    have hcl : IsClosed (tsupport w ∩ (A.chart j) ⁻¹' tsupport (β p)) :=
      ((A.chart j).continuousOn.mono hwj).preimage_isClosed_of_isClosed (isClosed_tsupport w)
        (isClosed_tsupport _)
    refine (closure_minimal ?_ hcl).trans ?_
    · intro x hx
      rw [Function.mem_support, hwp] at hx
      exact ⟨subset_tsupport _ (right_ne_zero_of_mul hx), subset_tsupport _ (left_ne_zero_of_mul hx)⟩
    · rintro x ⟨hx1, hx2⟩
      exact ⟨hwj hx1, hβ p hx2⟩
  have hL := integralWith_cons_sum A χ Φ hΦ Finset.univ wp hwps hwc hwpw
  rw [hsum] at hL
  rw [hL]
  refine Finset.sum_eq_zero fun p _ => ?_
  refine piece_eq_zero A χ Φ hΦ j _ ((A.chart j).isOpen_inter_preimage (hOo p.1)) inter_subset_left
    (fun _ => (A.chart j).symm p.1) ?_ (wp p) (hwps p)
    (hwc.of_isClosed_subset (isClosed_tsupport _) (hwpw p)) (hwpG p)
  intro i x hx
  have h1 := hx.2
  rw [mem_preimage, hO] at h1
  have h2 := mem_iInter.1 h1.2 i
  rwa [(A.chart j).left_inv hx.1] at h2

theorem stokes_compact_support [T2Space X] (A : FinHolAtlas (e + 1) X) (χ : ChartPartition A)
    (Φ : Fin e → LocPot X) (hΦ : ∀ i, IsPotential A (Φ i)) (w : X → ℝ) (hw : A.Smooth w)
    (hwc : HasCompactSupport w) :
    integralWith A χ (Fin.cons (LocPot.ofFun w) Φ) (fun _ => 1) = 0 := by
  have hsum : (fun x => ∑ j, χ.χ j x * w x) = w := by
    funext x; rw [← Finset.sum_mul, χ.sum_eq_one, one_mul]
  have hL := integralWith_cons_sum A χ Φ hΦ Finset.univ (fun j x => χ.χ j x * w x)
    (fun j => st_smooth_mul A (χ.smooth j) hw) hwc.isCompact (fun j => tsupport_mul_subset_right)
  rw [hsum] at hL
  rw [hL]
  refine Finset.sum_eq_zero fun j _ => ?_
  exact stokes_chart A χ Φ hΦ j _ (st_smooth_mul A (χ.smooth j) hw)
    (hwc.isCompact.of_isClosed_subset (isClosed_tsupport _) tsupport_mul_subset_right)
    (tsupport_mul_subset_left.trans (χ.tsupport_subset j))

end GroundTheory.Heights₂.Heights.FourB.CompactSupportStokes
