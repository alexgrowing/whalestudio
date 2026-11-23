import Mathlib
import ReciprocityTheory.AnalyticForms.LeviForms.ConvExpandStatement
open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Ar.Giv

noncomputable section

open scoped ENNReal

theorem cpt_chart_piece {e : ℕ} {X : Type} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    {T O C : Set (Fin e → ℂ)} (hT : IsOpen T) {s : (Fin e → ℂ) → X} (hs : ContinuousOn s T)
    {w : (Fin e → ℂ) → ℝ} (hO : MeasurableSet O) (hCm : MeasurableSet C) (hCT : C ⊆ T)
    (hw : ContinuousOn w C) (hw0 : ∀ y ∈ T ∩ O, w y ≤ 0)
    {G : X → ℝ} (hG : Measurable G) (hGz : ∀ y ∈ T, y ∉ O → y ∉ C → G (s y) = 0) :
    (Integrable G (((volume.restrict T).withDensity fun y => ENNReal.ofReal (w y)).map s) ↔
      IntegrableOn (fun y => G (s y) * max (w y) 0) C) ∧
    ∫ x, G x ∂(((volume.restrict T).withDensity fun y => ENNReal.ofReal (w y)).map s) =
      ∫ y in C, G (s y) * max (w y) 0 := by
  have hTm : MeasurableSet T := hT.measurableSet
  have hsm : AEMeasurable s ((volume.restrict T).withDensity fun y => ENNReal.ofReal (w y)) :=
    (hs.aemeasurable hTm).mono_ac (withDensity_absolutelyContinuous _ _)
  have hGm := hG.aestronglyMeasurable
    (μ := ((volume.restrict T).withDensity fun y => ENNReal.ofReal (w y)).map s)
  have h1 : ((volume.restrict T).withDensity fun y => ENNReal.ofReal (w y)) (T ∩ O) = 0 := by
    rw [withDensity_apply _ (hTm.inter hO)]
    refine (setLIntegral_congr_fun (g := fun _ => 0) (hTm.inter hO) ?_).trans (by simp)
    intro y hy
    exact ENNReal.ofReal_of_nonpos (hw0 y hy)
  have h2 : ((volume.restrict T).withDensity fun y => ENNReal.ofReal (w y)) Tᶜ = 0 :=
    withDensity_absolutelyContinuous _ _ (by
      rw [Measure.restrict_apply hTm.compl]; simp)
  have hae : (G ∘ s) =ᵐ[(volume.restrict T).withDensity fun y => ENNReal.ofReal (w y)]
      C.indicator (G ∘ s) := by
    have h3 := measure_union_null h1 h2
    refine measure_mono_null (fun y hy => ?_) h3
    by_contra hcon
    simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_compl_iff, not_or, not_and,
      not_not] at hcon
    have hyT : y ∈ T := hcon.2
    have hyO : y ∉ O := hcon.1 hyT
    apply hy
    by_cases hyC : y ∈ C
    · simp [Set.indicator_of_mem hyC]
    · simp [Set.indicator_of_notMem hyC, hGz y hyT hyO hyC]
  have hrest : ((volume.restrict T).withDensity fun y => ENNReal.ofReal (w y)).restrict C =
      (volume.restrict C).withDensity fun y => ENNReal.ofReal (w y) := by
    rw [restrict_withDensity hCm, Measure.restrict_restrict hCm, Set.inter_eq_left.2 hCT]
  have hwm : AEMeasurable (fun y => (w y).toNNReal) (volume.restrict C) :=
    (hw.aemeasurable hCm).real_toNNReal
  have hofR : (fun y => ENNReal.ofReal (w y)) = fun y => ((w y).toNNReal : ℝ≥0∞) := rfl
  have hsm2 : (fun y => (w y).toNNReal • (G ∘ s) y) = fun y => G (s y) * max (w y) 0 := by
    funext y
    simp [NNReal.smul_def, Real.coe_toNNReal', mul_comm]
  constructor
  · rw [integrable_map_measure hGm hsm, integrable_congr hae, integrable_indicator_iff hCm,
      IntegrableOn, hrest, hofR, integrable_withDensity_iff_integrable_smul₀ hwm, hsm2]
    rfl
  · rw [integral_map hsm hGm]
    refine Eq.trans (integral_congr_ae hae) ?_
    rw [integral_indicator hCm, hrest, hofR, integral_withDensity_eq_integral_smul₀ hwm, hsm2]

variable {e : ℕ} {X : Type} [TopologicalSpace X]

def cptSet (A : FinHolAtlas e X) (P : ChartPartition A) (K : Set X) (j : Fin A.n) :
    Set (Fin e → ℂ) :=
  A.chart j '' (K ∩ tsupport (P.χ j))

def cptW (A : FinHolAtlas e X) (P : ChartPartition A) (Φ : Fin e → LocPot X) (j : Fin A.n)
    (y : Fin e → ℂ) : ℝ :=
  P.χ j ((A.chart j).symm y) * locDens A Φ j y

theorem cptSet_symm_mem (A : FinHolAtlas e X) (P : ChartPartition A) (K : Set X) (j : Fin A.n)
    {y : Fin e → ℂ} (hy : y ∈ cptSet A P K j) : (A.chart j).symm y ∈ K := by
  obtain ⟨x, ⟨hxK, hxs⟩, rfl⟩ := hy
  rw [(A.chart j).left_inv (P.tsupport_subset j hxs)]
  exact hxK

theorem cptSet_subset_target (A : FinHolAtlas e X) (P : ChartPartition A) (K : Set X) (j : Fin A.n) :
    cptSet A P K j ⊆ (A.chart j).target := by
  rintro y ⟨x, ⟨-, hxs⟩, rfl⟩
  exact (A.chart j).map_source (P.tsupport_subset j hxs)

theorem cptSet_compact [CompactSpace X] (A : FinHolAtlas e X) (P : ChartPartition A) {K : Set X}
    (hK : IsClosed K) (j : Fin A.n) : IsCompact (cptSet A P K j) := by
  exact (hK.isCompact.inter_right (isClosed_tsupport _)).image_of_continuousOn
    ((A.chart j).continuousOn.mono fun x hx => P.tsupport_subset j hx.2)

theorem cptSet_subset (A : FinHolAtlas e X) (P : ChartPartition A) {K U : Set X} (hKU : K ⊆ U)
    (j : Fin A.n) : cptSet A P K j ⊆ (A.chart j).target ∩ (A.chart j).symm ⁻¹' U := by
  intro y hy
  exact ⟨cptSet_subset_target A P K j hy, hKU (cptSet_symm_mem A P K j hy)⟩

theorem cptW_continuousOn (A : FinHolAtlas e X) (P : ChartPartition A) (Φ : Fin e → LocPot X)
    {K U : Set X} (hKU : K ⊆ U) (j : Fin A.n)
    (hc : ContinuousOn (locDens A Φ j) ((A.chart j).target ∩ (A.chart j).symm ⁻¹' U)) :
    ContinuousOn (cptW A P Φ j) (cptSet A P K j) := by
  have hχ : ContinuousOn (fun y => P.χ j ((A.chart j).symm y)) (cptSet A P K j) :=
    ((P.smooth j) j).continuousOn.mono fun y hy => ⟨cptSet_subset_target A P K j hy, Set.mem_univ _⟩
  exact hχ.mul (hc.mono (cptSet_subset A P hKU j))

variable [MeasurableSpace X] [BorelSpace X]

theorem cpt_chartMeasure [CompactSpace X] (A : FinHolAtlas e X) (P : ChartPartition A)
    (Φ : Fin e → LocPot X) {K U : Set X} (hK : IsClosed K) (hKU : K ⊆ U) (j : Fin A.n)
    (hc : ContinuousOn (locDens A Φ j) ((A.chart j).target ∩ (A.chart j).symm ⁻¹' U))
    {G : X → ℝ} (hG : Measurable G) (hGK : ∀ x, x ∉ K → G x = 0) :
    (Integrable G (chartMeasure A P Φ j) ↔
      IntegrableOn (fun y => G ((A.chart j).symm y) * max (cptW A P Φ j y) 0) (cptSet A P K j)) ∧
    ∫ x, G x ∂chartMeasure A P Φ j =
      ∫ y in cptSet A P K j, G ((A.chart j).symm y) * max (cptW A P Φ j y) 0 := by
  have key := cpt_chart_piece (w := cptW A P Φ j) (s := (A.chart j).symm) (G := G)
    (T := (A.chart j).target) (C := cptSet A P K j)
    (O := (A.chart j).target ∩ (A.chart j).symm ⁻¹' (tsupport (P.χ j))ᶜ)
    (A.chart j).open_target (A.chart j).continuousOn_symm
    ((A.chart j).isOpen_inter_preimage_symm (isClosed_tsupport _).isOpen_compl).measurableSet
    (cptSet_compact A P hK j).measurableSet (cptSet_subset_target A P K j)
    (cptW_continuousOn A P Φ hKU j hc)
    (by
      rintro y ⟨-, -, hy⟩
      have h0 : P.χ j ((A.chart j).symm y) = 0 := image_eq_zero_of_notMem_tsupport hy
      simp [cptW, h0])
    hG
    (by
      intro y hy hyO hyC
      by_contra hne
      have hxK : (A.chart j).symm y ∈ K := by
        by_contra h
        exact hne (hGK _ h)
      have hxs : (A.chart j).symm y ∈ tsupport (P.χ j) := by
        by_contra h
        exact hyO ⟨hy, h⟩
      exact hyC ⟨_, ⟨hxK, hxs⟩, (A.chart j).right_inv hy⟩)
  exact key

theorem cpt_aesm [CompactSpace X] (A : FinHolAtlas e X) (P : ChartPartition A)
    (Φ : Fin e → LocPot X) {K U : Set X} (hK : IsClosed K) (hKU : K ⊆ U) (j : Fin A.n)
    (hc : ContinuousOn (locDens A Φ j) ((A.chart j).target ∩ (A.chart j).symm ⁻¹' U))
    {G : X → ℝ} (hG : Measurable G) :
    AEStronglyMeasurable (fun y => G ((A.chart j).symm y) * max (cptW A P Φ j y) 0)
      (volume.restrict (cptSet A P K j)) := by
  have hCm : MeasurableSet (cptSet A P K j) := (cptSet_compact A P hK j).isClosed.measurableSet
  have hs : ContinuousOn (A.chart j).symm (cptSet A P K j) :=
    (A.chart j).continuousOn_symm.mono (cptSet_subset_target A P K j)
  have h1 : AEMeasurable (fun y => G ((A.chart j).symm y)) (volume.restrict (cptSet A P K j)) :=
    hG.comp_aemeasurable (hs.aemeasurable hCm)
  have h2 : AEMeasurable (fun y => max (cptW A P Φ j y) 0) (volume.restrict (cptSet A P K j)) :=
    ((cptW_continuousOn A P Φ hKU j hc).aemeasurable hCm).max aemeasurable_const
  exact (h1.mul h2).aestronglyMeasurable

theorem cpt_abs_max {c a B : ℝ} (hc : 0 ≤ c) (hc1 : c ≤ 1) (h : |a| ≤ B) :
    |max (c * a) 0| ≤ B := by
  have hB : 0 ≤ B := le_trans (abs_nonneg a) h
  rw [abs_of_nonneg (le_max_right _ _)]
  refine max_le ?_ hB
  calc c * a ≤ |c * a| := le_abs_self _
    _ = c * |a| := by rw [abs_mul, abs_of_nonneg hc]
    _ ≤ 1 * |a| := mul_le_mul_of_nonneg_right hc1 (abs_nonneg a)
    _ ≤ B := by rw [one_mul]; exact h

theorem cpt_integrableOn [CompactSpace X] (A : FinHolAtlas e X) (P : ChartPartition A)
    (Φ : Fin e → LocPot X) {K U : Set X} (hK : IsClosed K) (hKU : K ⊆ U) (j : Fin A.n)
    (hc : ContinuousOn (locDens A Φ j) ((A.chart j).target ∩ (A.chart j).symm ⁻¹' U))
    {G : X → ℝ} (hG : Measurable G) {B : ℝ} (hB : ∀ x ∈ K, |G x| ≤ B) :
    IntegrableOn (fun y => G ((A.chart j).symm y) * max (cptW A P Φ j y) 0) (cptSet A P K j) := by
  have hCc := cptSet_compact A P hK j
  obtain ⟨L, hL⟩ := hCc.exists_bound_of_continuousOn
    (hc.mono (cptSet_subset A P hKU j))
  haveI : IsFiniteMeasure (volume.restrict (cptSet A P K j)) :=
    ⟨by simpa using hCc.measure_lt_top⟩
  refine Integrable.of_bound (cpt_aesm A P Φ hK hKU j hc hG) (B * L)
    (ae_restrict_of_forall_mem hCc.measurableSet fun y hy => ?_)
  have hx := cptSet_symm_mem A P K j hy
  have a2 : |max (cptW A P Φ j y) 0| ≤ L :=
    cpt_abs_max (P.nonneg j _) (chi_le_one P j _) (by simpa [Real.norm_eq_abs] using hL y hy)
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul (hB _ hx) a2 (abs_nonneg _) ((abs_nonneg _).trans (hB _ hx))

theorem cpt_maMeasure [CompactSpace X] (A : FinHolAtlas e X) (hne : Nonempty (ChartPartition A))
    (Φ : Fin e → LocPot X) {K U : Set X} (hK : IsClosed K) (hKU : K ⊆ U)
    (hc : ∀ j, ContinuousOn (locDens A Φ j) ((A.chart j).target ∩ (A.chart j).symm ⁻¹' U))
    {G : X → ℝ} (hG : Measurable G) (hGK : ∀ x, x ∉ K → G x = 0) {B : ℝ}
    (hB : ∀ x ∈ K, |G x| ≤ B) :
    Integrable G (maMeasure A Φ) ∧ ∫ x, G x ∂maMeasure A Φ =
      ∑ j, ∫ y in cptSet A hne.some K j,
        G ((A.chart j).symm y) * max (cptW A hne.some Φ j y) 0 := by
  have hint : ∀ j, Integrable G (chartMeasure A hne.some Φ j) := fun j =>
    (cpt_chartMeasure A hne.some Φ hK hKU j (hc j) hG hGK).1.2
      (cpt_integrableOn A hne.some Φ hK hKU j (hc j) hG hB)
  rw [maMeasure_eq_sum A Φ hne]
  refine ⟨integrable_finset_sum_measure.2 fun j _ => hint j, ?_⟩
  rw [integral_finset_sum_measure fun j _ => hint j]
  exact Finset.sum_congr rfl fun j _ => (cpt_chartMeasure A hne.some Φ hK hKU j (hc j) hG hGK).2

theorem cpt_meas {U S : Set X} (hU : IsOpen U) (hS : MeasurableSet S) (hSU : S ⊆ U) {f : X → ℝ}
    (hf : ContinuousOn f U) : Measurable (S.indicator f) := by
  classical
  have h1 : Measurable (U.piecewise f 0) :=
    hf.measurable_piecewise (continuousOn_const (c := (0 : ℝ))) hU.measurableSet
  have h2 : S.indicator f = S.indicator (U.piecewise f 0) := by
    funext x
    by_cases hx : x ∈ S
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, Set.piecewise_eq_of_mem _ _ _ (hSU hx)]
    · simp only [Set.indicator_apply, hx, if_false]
  rw [h2]
  exact h1.indicator hS

theorem cpt_ind [CompactSpace X] [T2Space X] (A : FinHolAtlas e X)
    (hne : Nonempty (ChartPartition A)) (Φ : Fin e → LocPot X) {K U S : Set X} (hU : IsOpen U)
    (hK : IsCompact K) (hKU : K ⊆ U)
    (hc : ∀ j, ContinuousOn (locDens A Φ j) ((A.chart j).target ∩ (A.chart j).symm ⁻¹' U))
    (hS : MeasurableSet S) (hSK : S ⊆ K) {f : X → ℝ} (hf : ContinuousOn f U) :
    Integrable (S.indicator f) (maMeasure A Φ) ∧ ∫ x in S, f x ∂maMeasure A Φ =
      ∑ j, ∫ y in cptSet A hne.some K j,
        S.indicator f ((A.chart j).symm y) * max (cptW A hne.some Φ j y) 0 := by
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (hf.mono hKU)
  have hb : ∀ x ∈ K, |S.indicator f x| ≤ M := fun x hx => by
    by_cases hxS : x ∈ S
    · simpa [Set.indicator_of_mem hxS, Real.norm_eq_abs] using hM x hx
    · rw [Set.indicator_of_notMem hxS, abs_zero]
      exact (norm_nonneg _).trans (hM x hx)
  have key := cpt_maMeasure A hne Φ hK.isClosed hKU hc (cpt_meas hU hS (hSK.trans hKU) hf)
    (fun x hx => Set.indicator_of_notMem (fun h => hx (hSK h)) _) hb
  refine ⟨key.1, ?_⟩
  rw [← integral_indicator hS]
  exact key.2

theorem cpt_chart_tendsto [CompactSpace X] (A : FinHolAtlas e X) (P : ChartPartition A)
    (Φ : Fin e → LocPot X) (ΦT : ℝ → Fin e → LocPot X) {K U E : Set X} (hU : IsOpen U)
    (hK : IsCompact K) (hKc : IsClosed K) (hKU : K ⊆ U) (j : Fin A.n)
    (hc : ContinuousOn (locDens A Φ j) ((A.chart j).target ∩ (A.chart j).symm ⁻¹' U))
    (hpot : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ i, IsPotential A (ΦT t i))
    (hld : TendstoUniformlyOn (fun t => locDens A (ΦT t) j) (locDens A Φ j) (𝓝[>] 0)
      (cptSet A P K j))
    {g : X → ℝ} {gT : ℝ → X → ℝ} (hgT : ∀ t, ContinuousOn (gT t) U) (hgc : ContinuousOn g U)
    (hgU : TendstoUniformlyOn gT g (𝓝[>] 0) K) (hE : MeasurableSet E) (hEK : E ⊆ K) :
    Tendsto (fun t => ∫ y in cptSet A P K j,
        E.indicator (gT t) ((A.chart j).symm y) * max (cptW A P (ΦT t) j y) 0) (𝓝[>] 0)
      (𝓝 (∫ y in cptSet A P K j,
        E.indicator g ((A.chart j).symm y) * max (cptW A P Φ j y) 0)) := by
  have hCc := cptSet_compact A P hKc j
  have hCm := hCc.measurableSet
  have hCV := cptSet_subset A P hKU j
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (hgc.mono hKU)
  obtain ⟨L, hL⟩ := hCc.exists_bound_of_continuousOn (hc.mono hCV)
  refine tendsto_integral_filter_of_dominated_convergence (fun _ => (M + 1) * (L + 1)) ?_ ?_ ?_ ?_
  · filter_upwards [hpot] with t ht
    exact cpt_aesm A P (ΦT t) hKc hKU j
      ((locDensCont A _ ht j).mono Set.inter_subset_left)
      (cpt_meas hU hE (hEK.trans hKU) (hgT t))
  · have h1 := Metric.tendstoUniformlyOn_iff.1 hgU 1 one_pos
    have h2 := Metric.tendstoUniformlyOn_iff.1 hld 1 one_pos
    filter_upwards [h1, h2] with t ht1 ht2
    refine ae_restrict_of_forall_mem hCm fun y hy => ?_
    have hx := cptSet_symm_mem A P K j hy
    have hMx := hM _ hx
    have hLy := hL y hy
    rw [Real.norm_eq_abs] at hMx hLy
    have hd1 := ht1 _ hx
    have hd2 := ht2 y hy
    rw [Real.dist_eq, abs_lt] at hd1 hd2
    have a1 : |E.indicator (gT t) ((A.chart j).symm y)| ≤ M + 1 := by
      by_cases hxE : (A.chart j).symm y ∈ E
      · rw [Set.indicator_of_mem hxE]
        rw [abs_le] at hMx ⊢
        constructor <;> linarith [hd1.1, hd1.2, hMx.1, hMx.2]
      · rw [Set.indicator_of_notMem hxE, abs_zero]
        linarith [abs_nonneg (g ((A.chart j).symm y))]
    have a2 : |max (cptW A P (ΦT t) j y) 0| ≤ L + 1 := by
      refine cpt_abs_max (P.nonneg j _) (chi_le_one P j _) ?_
      rw [abs_le] at hLy ⊢
      constructor <;> linarith [hd2.1, hd2.2, hLy.1, hLy.2]
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul a1 a2 (abs_nonneg _) ((abs_nonneg _).trans a1)
  · exact integrableOn_const hCc.measure_lt_top.ne
  · refine ae_restrict_of_forall_mem hCm fun y hy => ?_
    have hx := cptSet_symm_mem A P K j hy
    have l1 : Tendsto (fun t => E.indicator (gT t) ((A.chart j).symm y)) (𝓝[>] 0)
        (𝓝 (E.indicator g ((A.chart j).symm y))) := by
      by_cases hxE : (A.chart j).symm y ∈ E
      · simp only [Set.indicator_of_mem hxE]
        exact hgU.tendsto_at hx
      · simp only [Set.indicator_of_notMem hxE]
        exact tendsto_const_nhds
    have l2 : Tendsto (fun t => locDens A (ΦT t) j y) (𝓝[>] 0) (𝓝 (locDens A Φ j y)) :=
      hld.tendsto_at hy
    exact l1.mul (((l2.const_mul _)).max tendsto_const_nhds)

theorem compact_part_integrals_tendsto :
    ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] [MeasurableSpace X]
      [BorelSpace X] (A : FinHolAtlas e X) (U : Set X) (Φ : Fin e → LocPot X)
      (ΦT : ℝ → Fin e → LocPot X), IsOpen U →
      (∀ j, ContinuousOn (locDens A Φ j) ((A.chart j).target ∩ (A.chart j).symm ⁻¹' U)) →
      (∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ i, IsPotential A (ΦT t i)) →
      (∀ j, ∀ K ⊆ (A.chart j).target ∩ (A.chart j).symm ⁻¹' U, IsCompact K →
        TendstoUniformlyOn (fun t => locDens A (ΦT t) j) (locDens A Φ j) (𝓝[>] 0) K) →
      ∀ (g : X → ℝ) (gT : ℝ → X → ℝ), (∀ t, ContinuousOn (gT t) U) →
        TendstoLocallyUniformlyOn gT g (𝓝[>] 0) U →
        ∀ K E : Set X, IsCompact K → K ⊆ U → MeasurableSet E → E ⊆ K →
          maMeasure A Φ K < ⊤ ∧ IntegrableOn g K (maMeasure A Φ) ∧
            Tendsto (fun t => ∫ y in E, gT t y ∂maMeasure A (ΦT t)) (𝓝[>] 0)
              (𝓝 (∫ y in E, g y ∂maMeasure A Φ)) := by
  intro e X _ _ _ _ _ A U Φ ΦT hU hc hpot hunif g gT hgT hlim K E hK hKU hE hEK
  have hne : Nonempty (ChartPartition A) := existsPartition A
  have hKc : IsClosed K := hK.isClosed
  have hKm : MeasurableSet K := hKc.measurableSet
  have hgc : ContinuousOn g U := hlim.continuousOn (Eventually.of_forall hgT).frequently
  have hgU : TendstoUniformlyOn gT g (𝓝[>] 0) K :=
    (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK).1 (hlim.mono hKU)
  have c1 := cpt_ind A hne Φ hU hK hKU hc hKm subset_rfl (f := fun _ => (1 : ℝ)) continuousOn_const
  have c2 := cpt_ind A hne Φ hU hK hKU hc hKm subset_rfl hgc
  have c3 := cpt_ind A hne Φ hU hK hKU hc hE hEK hgc
  refine ⟨?_, (integrable_indicator_iff hKm).1 c2.1, ?_⟩
  · have h := (integrable_indicator_iff hKm).1 c1.1
    exact ((integrableOn_const_iff (by simp)).1 h).resolve_left (by simp)
  · rw [c3.2]
    refine Tendsto.congr' ?_ (tendsto_finset_sum _ fun j _ =>
      cpt_chart_tendsto A hne.some Φ ΦT hU hK hKc hKU j (hc j) hpot
        (hunif j _ (cptSet_subset A hne.some hKU j) (cptSet_compact A hne.some hKc j))
        hgT hgc hgU hE hEK)
    filter_upwards [hpot] with t ht
    exact (cpt_ind A hne (ΦT t) hU hK hKU
      (fun j => (locDensCont A _ ht j).mono Set.inter_subset_left) hE hEK (hgT t)).2.symm

end

end GlobalTheory.CompanionTheory.Ar.Giv
