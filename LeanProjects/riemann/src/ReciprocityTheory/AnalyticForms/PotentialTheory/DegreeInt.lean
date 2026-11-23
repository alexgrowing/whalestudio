import ReciprocityTheory.AnalyticForms.PotentialTheory.Degree
import ReciprocityTheory.AnalyticForms.PotentialTheory.PotentialContDiffAt
import ReciprocityTheory.AnalyticForms.PotentialTheory.LocDens
import ReciprocityTheory.AnalyticForms.PotentialTheory.DegreeIntB

namespace ReciprocityTheory.AnForm.M

open MeasureTheory FinHolAtlas Filter Topology

noncomputable section

variable {e : ℕ} {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

theorem integralWith_localize_support [CompactSpace X] [T2Space X] (A : FinHolAtlas e X)
    (P : ChartPartition A) (Φ : Fin e → LocPot X) (hΦ : ∀ i, IsPotential A (Φ i))
    (k : Fin A.n) (g : X → ℝ) (hg : ∀ x, x ∉ (A.chart k).source → g x = 0)
    (hint : IntegrableOn (fun z => g ((A.chart k).symm z) * locDens A Φ k z)
      (A.chart k).target) :
    (∀ j, IntegrableOn (fun y => P.χ j ((A.chart j).symm y) * g ((A.chart j).symm y) *
      locDens A Φ j y) (A.chart j).target) ∧
    integralWith A P Φ g = ∫ z in (A.chart k).target, g ((A.chart k).symm z) * locDens A Φ k z := by
  have hD := dI_chartDens_locDens A Φ hΦ
  have hk : ∀ j, IntegrableOn (fun y => P.χ j ((A.chart k).symm y) * g ((A.chart k).symm y) *
      locDens A Φ k y) (A.chart k).target := by
    intro j
    have hm : AEStronglyMeasurable (fun y => P.χ j ((A.chart k).symm y))
        (volume.restrict (A.chart k).target) :=
      (dI_chi_contOn A P j k).aestronglyMeasurable (A.chart k).open_target.measurableSet
    have hb : IntegrableOn (fun y => P.χ j ((A.chart k).symm y) *
        (g ((A.chart k).symm y) * locDens A Φ k y)) (A.chart k).target := by
      refine hint.norm.mono' (hm.mul hint.aestronglyMeasurable) (ae_of_all _ fun y => ?_)
      rw [norm_mul]
      refine mul_le_of_le_one_left (norm_nonneg _) ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (P.nonneg j _)]
      exact dI_chi_le_one A P j _
    simpa only [mul_assoc] using hb
  have htr := fun j => dI_transfer A hD k j (fun x => P.χ j x * g x)
    (fun x hx => by simp only [hg x hx, mul_zero]) (hk j)
  refine ⟨fun j => (htr j).1, ?_⟩
  have h2 : ∀ j, ∫ y in (A.chart j).target, P.χ j ((A.chart j).symm y) *
      g ((A.chart j).symm y) * locDens A Φ j y =
      ∫ y in (A.chart k).target, P.χ j ((A.chart k).symm y) * g ((A.chart k).symm y) *
        locDens A Φ k y := by
    intro j
    refine (htr j).2.trans ?_
    symm
    refine setIntegral_eq_of_subset_of_forall_diff_eq_zero
      (A.chart k).open_target.measurableSet Set.inter_subset_left ?_
    intro y hy
    have hys : (A.chart k).symm y ∉ (A.chart j).source := fun hs => hy.2 ⟨hy.1, hs⟩
    simp only [dI_chi_zero A P j hys, zero_mul]
  change ∑ j, ∫ y in (A.chart j).target, P.χ j ((A.chart j).symm y) *
      g ((A.chart j).symm y) * locDens A Φ j y = _
  rw [Finset.sum_congr rfl (fun j _ => h2 j),
    ← integral_finset_sum Finset.univ (fun j _ => hk j)]
  congr 1
  funext y
  simp only [← Finset.sum_mul, P.sum_eq_one, one_mul]

theorem exists_sheet_partition [CompactSpace Y] [T2Space Y] [CompactSpace X] [T2Space X]
    {A : FinHolAtlas e X} {B : FinHolAtlas e Y} {h : Y → X} (hh : HoloMap B A h) {d : ℕ}
    {S : Set X} (hd : IsDegreeOff A B h d S) [MeasurableSpace X] [BorelSpace X] [Nonempty X] :
    ∃ (E V : ℕ → Set X) (k : ℕ → Fin A.n) (W : ℕ → Fin d → Set Y) (j : ℕ → Fin d → Fin B.n),
      (∀ m, MeasurableSet (E m)) ∧ Pairwise (Function.onFun Disjoint E) ∧
      (⋃ m, E m) = Sᶜ ∧ (∀ m, E m ⊆ V m) ∧
      ∀ m, IsOpen (V m) ∧ V m ⊆ (A.chart (k m)).source ∧ (∀ i, IsOpen (W m i)) ∧
        Pairwise (Function.onFun Disjoint (W m)) ∧ h ⁻¹' V m = ⋃ i, W m i ∧
        ∀ i, Set.BijOn h (W m i) (V m) ∧ W m i ⊆ (B.chart (j m i)).source := by
  classical
  haveI := dI_secondCountable A
  have hSc : (Sᶜ).Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty, Set.compl_empty_iff] at hne
    have h2 := hd.2.1
    rw [hne, interior_univ] at h2
    exact Set.univ_nonempty.ne_empty h2
  choose V0 hV0o hxV0 hV0S k0 hk0 W0 j0 hW0 hdis0 hpre0 hsh0 using
    fun x : ↥(Sᶜ) => dI_sheets hh hd (x : X) x.2
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable V0 hV0o
  have hTne : T.Nonempty := by
    obtain ⟨x0, hx0⟩ := hSc
    have hx : (x0 : X) ∈ ⋃ i ∈ T, V0 i := by
      rw [hTU]; exact Set.mem_iUnion.2 ⟨⟨x0, hx0⟩, hxV0 _⟩
    simp only [Set.mem_iUnion] at hx
    obtain ⟨i, hi, -⟩ := hx
    exact ⟨i, hi⟩
  obtain ⟨f, hf⟩ := hTc.exists_eq_range hTne
  subst hf
  rw [Set.biUnion_range] at hTU
  refine ⟨disjointed (fun m => V0 (f m)), fun m => V0 (f m), fun m => k0 (f m),
    fun m => W0 (f m), fun m => j0 (f m), ?_, ?_, ?_, ?_, ?_⟩
  · exact MeasurableSet.disjointed (fun n => (hV0o (f n)).measurableSet)
  · exact disjoint_disjointed _
  · rw [iUnion_disjointed]
    apply Set.Subset.antisymm
    · intro x hx
      obtain ⟨m, hm⟩ := Set.mem_iUnion.1 hx
      exact fun hxS => Set.disjoint_left.1 (hV0S (f m)) hm hxS
    · intro x hx
      have hx' : x ∈ ⋃ i, V0 i := Set.mem_iUnion.2 ⟨⟨x, hx⟩, hxV0 _⟩
      rw [← hTU] at hx'
      exact hx'
  · intro m
    first
      | exact disjointed_subset _ m
      | exact disjointed_le _ m
      | exact disjointed_subset m
  · intro m
    exact ⟨hV0o _, hk0 _, hW0 _, hdis0 _, hpre0 _, hsh0 _⟩

theorem degree_piece [CompactSpace Y] [T2Space Y] [CompactSpace X] [T2Space X]
    [MeasurableSpace X] [BorelSpace X]
    {A : FinHolAtlas e X} {B : FinHolAtlas e Y} {h : Y → X} (hh : HoloMap B A h) {d : ℕ}
    (Φ : Fin e → LocPot X) (hΦ : ∀ i, IsPotential A (Φ i)) (P : ChartPartition A)
    (Q : ChartPartition B) {E V : Set X} (hE : MeasurableSet E) (hEV : E ⊆ V) (hV : IsOpen V)
    {k : Fin A.n} (hVk : V ⊆ (A.chart k).source) {W : Fin d → Set Y} {j : Fin d → Fin B.n}
    (hW : ∀ i, IsOpen (W i)) (hdis : Pairwise (Function.onFun Disjoint W))
    (hpre : h ⁻¹' V = ⋃ i, W i) (hsh : ∀ i, Set.BijOn h (W i) V ∧ W i ⊆ (B.chart (j i)).source)
    (g : X → ℝ) (hg : MIntegrable A Φ g) :
    (∀ j', IntegrableOn (fun y => Q.χ j' ((B.chart j').symm y) *
        (E.indicator g (h ((B.chart j').symm y))) *
        locDens B (fun i => (Φ i).pullback h hh.1) j' y) (B.chart j').target) ∧
    integralWith B Q (fun i => (Φ i).pullback h hh.1) (fun y => E.indicator g (h y)) =
      d * integralWith A P Φ (E.indicator g) := by
  have hΨ : ∀ i, IsPotential B ((Φ i).pullback h hh.1) :=
    fun i => isPotentialPullback A B h hh (Φ i) (hΦ i)
  have hfX : IntegrableOn (fun z => E.indicator g ((A.chart k).symm z) * locDens A Φ k z)
      (A.chart k).target :=
    dI_indicator (A.chart k) hE g _ (dI_target_of_mIntegrable A Φ hΦ g hg k)
  have hf0 : ∀ x, x ∉ (A.chart k).source → E.indicator g x = 0 :=
    fun x hx => Set.indicator_of_notMem (fun h' => hx (hVk (hEV h'))) g
  have hIX := (integralWith_localize_support A P Φ hΦ k (E.indicator g) hf0 hfX).2
  have hsum : ∀ y, E.indicator g (h y) =
      ∑ i, (W i).indicator (fun y => E.indicator g (h y)) y := by
    intro y
    by_cases hy : h y ∈ E
    · have hyV : y ∈ h ⁻¹' V := hEV hy
      rw [hpre] at hyV
      obtain ⟨i0, hi0⟩ := Set.mem_iUnion.1 hyV
      rw [Finset.sum_eq_single i0 (fun i _ hi => Set.indicator_of_notMem
          (fun hiy => Set.disjoint_left.1 (show Disjoint (W i) (W i0) from hdis hi) hiy hi0) _)
        (fun h' => absurd (Finset.mem_univ i0) h'), Set.indicator_of_mem hi0]
    · rw [Set.indicator_of_notMem hy]
      exact (Finset.sum_eq_zero fun i _ => by simp [hy]).symm
  have hsheet : ∀ i, IntegrableOn (fun y => (W i).indicator (fun y => E.indicator g (h y))
        ((B.chart (j i)).symm y) * locDens B (fun i => (Φ i).pullback h hh.1) (j i) y)
        (B.chart (j i)).target ∧
      ∫ y in (B.chart (j i)).target, (W i).indicator (fun y => E.indicator g (h y))
        ((B.chart (j i)).symm y) * locDens B (fun i => (Φ i).pullback h hh.1) (j i) y =
        ∫ z in (A.chart k).target, E.indicator g ((A.chart k).symm z) * locDens A Φ k z := by
    intro i
    obtain ⟨hbij, hWj⟩ := hsh i
    have hSI := sheet_integral hh Φ hΦ (j i) k (hW i) hWj hVk hbij (E.indicator g)
    have hOim : IsOpen ((B.chart (j i)) '' W i) :=
      (B.chart (j i)).isOpen_image_of_subset_source (hW i) hWj
    have hVim : (A.chart k) '' V ⊆ (A.chart k).target := by
      rintro _ ⟨x, hx, rfl⟩; exact (A.chart k).map_source (hVk hx)
    have hWim : (B.chart (j i)) '' W i ⊆ (B.chart (j i)).target := by
      rintro _ ⟨w, hw, rfl⟩; exact (B.chart (j i)).map_source (hWj hw)
    have hint1 : IntegrableOn (fun y => E.indicator g (h ((B.chart (j i)).symm y)) *
        locDens B (fun i => (Φ i).pullback h hh.1) (j i) y) ((B.chart (j i)) '' W i) :=
      hSI.1.2 (hfX.mono_set hVim)
    have heqW : Set.EqOn (fun y => E.indicator g (h ((B.chart (j i)).symm y)) *
        locDens B (fun i => (Φ i).pullback h hh.1) (j i) y)
        (fun y => (W i).indicator (fun y => E.indicator g (h y)) ((B.chart (j i)).symm y) *
          locDens B (fun i => (Φ i).pullback h hh.1) (j i) y) ((B.chart (j i)) '' W i) := by
      rintro _ ⟨w, hw, rfl⟩
      simp only [(B.chart (j i)).left_inv (hWj hw), Set.indicator_of_mem hw]
    have hzeroW : ∀ y ∈ (B.chart (j i)).target \ (B.chart (j i)) '' W i,
        (W i).indicator (fun y => E.indicator g (h y)) ((B.chart (j i)).symm y) *
          locDens B (fun i => (Φ i).pullback h hh.1) (j i) y = 0 := by
      rintro y ⟨hy, hyW⟩
      have : (B.chart (j i)).symm y ∉ W i := fun h' => hyW ⟨_, h', (B.chart (j i)).right_inv hy⟩
      simp [Set.indicator_of_notMem this]
    have hzeroV : ∀ z ∈ (A.chart k).target \ (A.chart k) '' V,
        E.indicator g ((A.chart k).symm z) * locDens A Φ k z = 0 := by
      rintro z ⟨hz, hzV⟩
      have : (A.chart k).symm z ∉ E := fun h' => hzV ⟨_, hEV h', (A.chart k).right_inv hz⟩
      simp [Set.indicator_of_notMem this]
    refine ⟨(hint1.congr_fun heqW hOim.measurableSet).of_forall_sdiff_eq_zero
      (B.chart (j i)).open_target.measurableSet hzeroW, ?_⟩
    rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (B.chart (j i)).open_target.measurableSet
        hWim hzeroW, ← setIntegral_congr_fun hOim.measurableSet heqW, hSI.2,
      ← setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (A.chart k).open_target.measurableSet
        hVim hzeroV]
  have hloc := fun i => integralWith_localize_support B Q (fun i => (Φ i).pullback h hh.1) hΨ
    (j i) ((W i).indicator (fun y => E.indicator g (h y)))
    (fun y hy => Set.indicator_of_notMem (fun h' => hy ((hsh i).2 h')) _) (hsheet i).1
  have hpt : ∀ j' y, Q.χ j' ((B.chart j').symm y) * E.indicator g (h ((B.chart j').symm y)) *
      locDens B (fun i => (Φ i).pullback h hh.1) j' y =
      ∑ i, Q.χ j' ((B.chart j').symm y) *
        (W i).indicator (fun y => E.indicator g (h y)) ((B.chart j').symm y) *
        locDens B (fun i => (Φ i).pullback h hh.1) j' y := by
    intro j' y
    rw [hsum, Finset.mul_sum, Finset.sum_mul]
  refine ⟨fun j' => ?_, ?_⟩
  · have := integrable_finsetSum Finset.univ
      (f := fun i y => Q.χ j' ((B.chart j').symm y) *
        (W i).indicator (fun y => E.indicator g (h y)) ((B.chart j').symm y) *
        locDens B (fun i => (Φ i).pullback h hh.1) j' y) (fun i _ => (hloc i).1 j')
    exact IntegrableOn.congr_fun this (fun y _ => (hpt j' y).symm) (B.chart j').open_target.measurableSet
  · have h1 : integralWith B Q (fun i => (Φ i).pullback h hh.1) (fun y => E.indicator g (h y)) =
        ∑ i, integralWith B Q (fun i => (Φ i).pullback h hh.1)
          ((W i).indicator (fun y => E.indicator g (h y))) := by
      unfold integralWith
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun j' _ => ?_)
      rw [← integral_finsetSum _ (fun i _ => (hloc i).1 j')]
      exact setIntegral_congr_fun (B.chart j').open_target.measurableSet (fun y _ => hpt j' y)
    rw [h1, Finset.sum_congr rfl (fun i _ => (hloc i).2.trans (hsheet i).2), Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hIX]

theorem degreeFormulaInt : DegreeFormulaIntStatement := by
  intro e X Y _ _ _ _ _ _ A B h hh d S hd Φ hΦ g hg
  rcases isEmpty_or_nonempty X with hX | hX
  · have hY : IsEmpty Y := ⟨fun y => hX.false (h y)⟩
    have hA : ∀ k, (A.chart k).target = ∅ := fun k => by
      rw [← (A.chart k).image_source_eq_target, Set.eq_empty_of_isEmpty (A.chart k).source,
        Set.image_empty]
    have hB : ∀ k, (B.chart k).target = ∅ := fun k => by
      rw [← (B.chart k).image_source_eq_target, Set.eq_empty_of_isEmpty (B.chart k).source,
        Set.image_empty]
    refine ⟨fun j K hK _ => ?_, ?_⟩
    · rw [hB j, Set.subset_empty_iff] at hK
      rw [hK]
      exact integrableOn_empty
    · simp [mInt, integralWith, hA, hB]
  letI : MeasurableSpace X := borel X
  have : BorelSpace X := ⟨rfl⟩
  letI : MeasurableSpace Y := borel Y
  have : BorelSpace Y := ⟨rfl⟩
  have hΨ : ∀ i, IsPotential B ((Φ i).pullback h hh.1) :=
    fun i => isPotentialPullback A B h hh (Φ i) (hΦ i)
  obtain ⟨P⟩ := existsPartition A
  obtain ⟨Q⟩ := existsPartition B
  obtain ⟨E, V, k, W, j, hEm, hEd, hEU, hEV, hsh⟩ := exists_sheet_partition hh hd
  have hmh : Measurable h := hh.1.measurable
  have hpiece := fun m => degree_piece hh Φ hΦ P Q (hEm m) (hEV m) (hsh m).1 (hsh m).2.1
    (hsh m).2.2.1 (hsh m).2.2.2.1 (hsh m).2.2.2.2.1 (hsh m).2.2.2.2.2 g hg
  have hvX : ∀ m, IntegrableOn (fun z => (E m).indicator g ((A.chart (k m)).symm z) *
      locDens A Φ (k m) z) (A.chart (k m)).target :=
    fun m => dI_indicator (A.chart (k m)) (hEm m) g _ (dI_target_of_mIntegrable A Φ hΦ g hg (k m))
  obtain ⟨a, ha⟩ : ∃ a : ℕ → ℝ, ∀ m, a m = ∫ z in (A.chart (k m)).target,
      |(E m).indicator g ((A.chart (k m)).symm z)| * |locDens A Φ (k m) z| := ⟨_, fun m => rfl⟩
  have ha0 : ∀ m, 0 ≤ a m := fun m => by
    rw [ha]
    exact setIntegral_nonneg (A.chart (k m)).open_target.measurableSet
      (fun z _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
  have haloc : ∀ m, (∀ jj, IntegrableOn (fun z => P.χ jj ((A.chart jj).symm z) *
        |(E m).indicator g ((A.chart jj).symm z)| * |locDens A Φ jj z|) (A.chart jj).target) ∧
      ∑ jj, ∫ z in (A.chart jj).target, P.χ jj ((A.chart jj).symm z) *
        |(E m).indicator g ((A.chart jj).symm z)| * |locDens A Φ jj z| = a m := by
    intro m
    rw [ha]
    refine dI_localize A P (dI_chartDens_abs A (dI_chartDens_locDens A Φ hΦ)) (k m)
      (fun x => |(E m).indicator g x|) (fun x hx => ?_) ?_
    · rw [Set.indicator_of_notMem (fun h' => hx ((hsh m).2.1 (hEV m h'))), abs_zero]
    · refine IntegrableOn.congr_fun (hvX m).norm (fun z _ => ?_) (A.chart (k m)).open_target.measurableSet
      simp only [Real.norm_eq_abs, abs_mul]
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C = ∑ jj, ∫ z in (A.chart jj).target,
      ‖P.χ jj ((A.chart jj).symm z) * g ((A.chart jj).symm z) * locDens A Φ jj z‖ :=
    ⟨_, rfl⟩
  have hsumN : ∀ N, ∑ m ∈ Finset.range N, a m ≤ C := by
    intro N
    rw [hC]
    calc ∑ m ∈ Finset.range N, a m = ∑ jj, ∫ z in (A.chart jj).target, ∑ m ∈ Finset.range N,
          P.χ jj ((A.chart jj).symm z) * |(E m).indicator g ((A.chart jj).symm z)| *
            |locDens A Φ jj z| := by
          rw [Finset.sum_congr rfl (fun m _ => ((haloc m).2).symm), Finset.sum_comm]
          refine Finset.sum_congr rfl (fun jj _ => ?_)
          rw [integral_finsetSum _ (fun m _ => (haloc m).1 jj)]
      _ ≤ _ := by
          refine Finset.sum_le_sum (fun jj _ => ?_)
          refine integral_mono_of_nonneg (Eventually.of_forall fun z => ?_)
            (integrableOn_weight A P Φ g hg jj).norm (Eventually.of_forall fun z => ?_)
          · exact Finset.sum_nonneg (fun m _ =>
              mul_nonneg (mul_nonneg (P.nonneg jj _) (abs_nonneg _)) (abs_nonneg _))
          · simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (P.nonneg jj _)]
            rw [← Finset.sum_mul, ← Finset.mul_sum]
            exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
              (dI_sum_ind_le E hEd g _ N) (P.nonneg jj _)) (abs_nonneg _)
  have hfin : ∑' m, (d : ENNReal) * ENNReal.ofReal (a m) < ⊤ := by
    rw [ENNReal.tsum_mul_left]
    refine ENNReal.mul_lt_top (ENNReal.natCast_lt_top d) (lt_of_le_of_lt
      (ENNReal.tsum_le_of_sum_range_le (c := ENNReal.ofReal C) fun N => ?_) ENNReal.ofReal_lt_top)
    rw [← ENNReal.ofReal_sum_of_nonneg (fun m _ => ha0 m)]
    exact ENNReal.ofReal_le_ofReal (hsumN N)
  have hY : ∀ j', IntegrableOn (fun y => Q.χ j' ((B.chart j').symm y) * (g ∘ h) ((B.chart j').symm y) *
      locDens B (fun i => (Φ i).pullback h hh.1) j' y) (B.chart j').target := by
    intro j'
    have hRm : ∀ m, MeasurableSet ((B.chart j').target ∩ (B.chart j').symm ⁻¹' (h ⁻¹' E m)) :=
      fun m => dI_mset (B.chart j') (hmh (hEm m))
    have hRint : ∀ m, IntegrableOn (fun y => Q.χ j' ((B.chart j').symm y) *
        (g ∘ h) ((B.chart j').symm y) * locDens B (fun i => (Φ i).pullback h hh.1) j' y)
        ((B.chart j').target ∩ (B.chart j').symm ⁻¹' (h ⁻¹' E m)) := by
      intro m
      refine (((hpiece m).1 j').mono_set Set.inter_subset_left).congr_fun (fun y hy => ?_) (hRm m)
      simp only [Function.comp_apply]
      rw [Set.indicator_of_mem (show h ((B.chart j').symm y) ∈ E m from hy.2)]
    have hbound : ∀ m, ∫⁻ y in (B.chart j').target ∩ (B.chart j').symm ⁻¹' (h ⁻¹' E m),
        ‖Q.χ j' ((B.chart j').symm y) * (g ∘ h) ((B.chart j').symm y) *
          locDens B (fun i => (Φ i).pullback h hh.1) j' y‖ₑ ≤ d * ENNReal.ofReal (a m) := by
      intro m
      obtain ⟨hVo, hVk, hWo, hWd, hpre, hsh'⟩ := hsh m
      have s1 : ∫⁻ y in (B.chart j').target ∩ (B.chart j').symm ⁻¹' (h ⁻¹' E m),
          ‖Q.χ j' ((B.chart j').symm y) * (g ∘ h) ((B.chart j').symm y) *
            locDens B (fun i => (Φ i).pullback h hh.1) j' y‖ₑ ≤
          ∫⁻ y in (B.chart j').target ∩ (B.chart j').symm ⁻¹' (h ⁻¹' E m),
            ENNReal.ofReal |(E m).indicator g (h ((B.chart j').symm y))| *
              ENNReal.ofReal |locDens B (fun i => (Φ i).pullback h hh.1) j' y| := by
        refine setLIntegral_mono' (hRm m) (fun y hy => ?_)
        have hyE : h ((B.chart j').symm y) ∈ E m := hy.2
        simp only [Function.comp_apply, Set.indicator_of_mem hyE, enorm_mul,
          Real.enorm_eq_ofReal_abs]
        rw [mul_assoc]
        refine mul_le_of_le_one_left zero_le ?_
        exact ENNReal.ofReal_le_one.2 (by
          rw [abs_of_nonneg (Q.nonneg _ _)]; exact dI_chi_le_one B Q j' _)
      have s2 : (B.chart j').target ∩ (B.chart j').symm ⁻¹' (h ⁻¹' E m) ⊆
          ⋃ i, (B.chart j') '' (W m i ∩ (B.chart j').source) := by
        rintro y ⟨hyt, hyE⟩
        have hyV : (B.chart j').symm y ∈ h ⁻¹' V m := hEV m hyE
        rw [hpre] at hyV
        obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hyV
        exact Set.mem_iUnion.2 ⟨i, _, ⟨hi, (B.chart j').map_target hyt⟩,
          (B.chart j').right_inv hyt⟩
      have s3 : ∀ i, ∫⁻ y in (B.chart j') '' (W m i ∩ (B.chart j').source),
          ENNReal.ofReal |(E m).indicator g (h ((B.chart j').symm y))| *
            ENNReal.ofReal |locDens B (fun i => (Φ i).pullback h hh.1) j' y| ≤
          ENNReal.ofReal (a m) := by
        intro i
        have hW' : IsOpen (W m i ∩ (B.chart j').source) := (hWo i).inter (B.chart j').open_source
        have hbij : Set.BijOn h (W m i ∩ (B.chart j').source)
            (h '' (W m i ∩ (B.chart j').source)) :=
          ((hsh' i).1.injOn.mono Set.inter_subset_left).bijOn_image
        have hV' : h '' (W m i ∩ (B.chart j').source) ⊆ (A.chart (k m)).source := by
          rintro _ ⟨w, hw, rfl⟩; exact hVk ((hsh' i).1.mapsTo hw.1)
        have hSL := sheet_lintegral hh Φ hΦ j' (k m) hW' Set.inter_subset_right hV' hbij
          (fun x => ENNReal.ofReal |(E m).indicator g x|)
        have hn := ofReal_integral_norm_eq_lintegral_enorm (hvX m)
        have h2 : ∫ z in (A.chart (k m)).target,
            ‖(E m).indicator g ((A.chart (k m)).symm z) * locDens A Φ (k m) z‖ = a m := by
          rw [ha]
          refine setIntegral_congr_fun (A.chart (k m)).open_target.measurableSet (fun z _ => ?_)
          simp only [Real.norm_eq_abs, abs_mul]
        rw [h2] at hn
        calc ∫⁻ y in (B.chart j') '' (W m i ∩ (B.chart j').source),
              ENNReal.ofReal |(E m).indicator g (h ((B.chart j').symm y))| *
                ENNReal.ofReal |locDens B (fun i => (Φ i).pullback h hh.1) j' y|
            = ∫⁻ z in (A.chart (k m)) '' (h '' (W m i ∩ (B.chart j').source)),
              ENNReal.ofReal |(E m).indicator g ((A.chart (k m)).symm z)| *
                ENNReal.ofReal |locDens A Φ (k m) z| := hSL
          _ ≤ ∫⁻ z in (A.chart (k m)).target,
              ENNReal.ofReal |(E m).indicator g ((A.chart (k m)).symm z)| *
                ENNReal.ofReal |locDens A Φ (k m) z| :=
            lintegral_mono_set (by
              rintro _ ⟨x, hx, rfl⟩; exact (A.chart (k m)).map_source (hV' hx))
          _ = ENNReal.ofReal (a m) := by
            rw [hn]
            refine lintegral_congr (fun z => ?_)
            simp only [enorm_mul, Real.enorm_eq_ofReal_abs]
      calc _ ≤ _ := s1
        _ ≤ ∫⁻ y in ⋃ i, (B.chart j') '' (W m i ∩ (B.chart j').source),
              ENNReal.ofReal |(E m).indicator g (h ((B.chart j').symm y))| *
                ENNReal.ofReal |locDens B (fun i => (Φ i).pullback h hh.1) j' y| :=
            lintegral_mono_set s2
        _ ≤ ∑' i, ∫⁻ y in (B.chart j') '' (W m i ∩ (B.chart j').source),
              ENNReal.ofReal |(E m).indicator g (h ((B.chart j').symm y))| *
                ENNReal.ofReal |locDens B (fun i => (Φ i).pullback h hh.1) j' y| :=
            lintegral_iUnion_le _ _
        _ ≤ ∑' i : Fin d, ENNReal.ofReal (a m) := ENNReal.tsum_le_tsum s3
        _ = d * ENNReal.ofReal (a m) := by
            rw [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hU : IntegrableOn (fun y => Q.χ j' ((B.chart j').symm y) *
        (g ∘ h) ((B.chart j').symm y) * locDens B (fun i => (Φ i).pullback h hh.1) j' y)
        (⋃ m, (B.chart j').target ∩ (B.chart j').symm ⁻¹' (h ⁻¹' E m)) :=
      ⟨AEStronglyMeasurable.iUnion fun m => (hRint m).1,
        (lintegral_iUnion_le _ _).trans_lt ((ENNReal.tsum_le_tsum hbound).trans_lt hfin)⟩
    have hZ := analyticNull B (h ⁻¹' S) hd.2.2.1 hd.2.2.2.1 j'
    have hZint : IntegrableOn (fun y => Q.χ j' ((B.chart j').symm y) *
        (g ∘ h) ((B.chart j').symm y) * locDens B (fun i => (Φ i).pullback h hh.1) j' y)
        ((B.chart j') '' (h ⁻¹' S ∩ (B.chart j').source)) := by
      rw [IntegrableOn, Measure.restrict_eq_zero.2 hZ]
      exact integrable_zero_measure
    refine (hU.union hZint).mono_set (fun y hy => ?_)
    by_cases hyS : (B.chart j').symm y ∈ h ⁻¹' S
    · exact Or.inr ⟨_, ⟨hyS, (B.chart j').map_target hy⟩, (B.chart j').right_inv hy⟩
    · have hyU : h ((B.chart j').symm y) ∈ ⋃ m, E m := by rw [hEU]; exact hyS
      obtain ⟨m, hm⟩ := Set.mem_iUnion.1 hyU
      exact Or.inl (Set.mem_iUnion.2 ⟨m, hy, hm⟩)
  have hXsum : HasSum (fun m => integralWith A P Φ ((E m).indicator g)) (integralWith A P Φ g) :=
    dI_hasSum A P Φ g (fun jj => integrableOn_weight A P Φ g hg jj) E hEm hEd S
      (analyticNull A S hd.1 hd.2.1) hEU
  have hYsum := dI_hasSum B Q (fun i => (Φ i).pullback h hh.1) (g ∘ h) hY (fun m => h ⁻¹' E m)
    (fun m => hmh (hEm m)) (fun m m' hmm' => (hEd hmm').preimage h) (h ⁻¹' S)
    (analyticNull B (h ⁻¹' S) hd.2.2.1 hd.2.2.2.1)
    (by rw [← Set.preimage_iUnion, hEU, Set.preimage_compl])
  have key : ∀ m, integralWith B Q (fun i => (Φ i).pullback h hh.1)
      ((h ⁻¹' E m).indicator (g ∘ h)) = d * integralWith A P Φ ((E m).indicator g) := by
    intro m
    rw [show (h ⁻¹' E m).indicator (g ∘ h) = fun y => (E m).indicator g (h y) from
      funext fun y => Set.indicator_comp_right h]
    exact (hpiece m).2
  simp only [key] at hYsum
  have hMY : MIntegrable B (fun i => (Φ i).pullback h hh.1) (g ∘ h) := fun j' K hK _ =>
    (dI_target_of_weights B Q (dI_chartDens_locDens B _ hΨ) (g ∘ h) hY j').mono_set hK
  refine ⟨hMY, ?_⟩
  rw [mIntEq B Q _ hΨ (g ∘ h) hMY, mIntEq A P Φ hΦ g hg]
  exact HasSum.unique hYsum (hXsum.mul_left _)

theorem degreeFormula : DegreeFormulaStatement := by
  intro e X Y _ _ _ _ _ _ A B h hh d S hd Φ hΦ g hg
  have hI : MIntegrable A Φ g := by
    intro j K hK hKc
    have h1 : ContinuousOn (fun y => g ((A.chart j).symm y)) K :=
      hg.comp_continuousOn ((A.chart j).continuousOn_symm.mono hK)
    have h2 : ContinuousOn (locDens A Φ j) K := (locDensCont A Φ hΦ j).mono hK
    exact (h1.mul h2).integrableOn_compact hKc
  exact (degreeFormulaInt A B h hh d S hd Φ hΦ g hI).2

end

end ReciprocityTheory.AnForm.M
