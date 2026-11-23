import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsUnitHermOfDet
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanGramFibreMeasureFormulaStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InfiniteAdelesLocalRingTotallyReal
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRing
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHaarMeasure
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HermitianMatricesLocallyCompactBorel
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TensTop

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Coef
open scoped TensorProduct ENNReal Topology

namespace GlobalTheory.CompanionTheory.SiegelND.Coef.AvgInf

section Abs

variable {V R : Type} [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V]
  [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R]

theorem fibre_compl_null {μ : Measure V} {ν : Measure R} {q : V → R} {m : R → Measure V} {U : Set V} {B : Set R}
    (hf : IsFibreFamily μ q id U ν B m) (s : R) : m s Uᶜ = 0 :=
  measure_mono_null (Set.compl_subset_compl.2 Set.inter_subset_right) (hf.1 s)

theorem measurable_fibre_lintegral [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V]
    {μ : Measure V} {ν : Measure R} {q : V → R} {m : R → Measure V} {U : Set V} {B : Set R} (hU : IsOpen U)
    (hB : IsOpen B) (hf : IsFibreFamily μ q id U ν B m) {h : V → ℝ} (hc : Continuous h) (h0 : ∀ X, 0 ≤ h X) :
    Measurable (B.indicator fun s => ∫⁻ X, ENNReal.ofReal (h X) ∂(m s)) := by
  classical
  have hnull := fibre_compl_null hf
  obtain ⟨-, -, h3⟩ := hf
  haveI : LocallyCompactSpace U := hU.locallyCompactSpace
  let K := CompactExhaustion.choice U
  let L : ℕ → Set V := fun n => Subtype.val '' K n
  let W : ℕ → Set V := fun n => Subtype.val '' interior (K (n + 1))
  have hLc : ∀ n, IsCompact (L n) := fun n => (K.isCompact n).image continuous_subtype_val
  have hWo : ∀ n, IsOpen (W n) := fun n => hU.isOpenMap_subtype_val _ isOpen_interior
  have hLW : ∀ n, L n ⊆ W n := fun n => Set.image_mono (K.subset_interior_succ n)
  have hWL : ∀ n, W n ⊆ L (n + 1) := fun n => Set.image_mono interior_subset
  have hWU : ∀ n, W n ⊆ U := by
    rintro n _ ⟨x, -, rfl⟩
    exact x.2
  choose f hf1 hfc hfs hf01 using fun n =>
    exists_continuousMap_one_of_isCompact_subset_isOpen (hLc n) (hWo n) (hLW n)
  have hmono : ∀ n X, f n X ≤ f (n + 1) X := by
    intro n X
    by_cases hX : X ∈ L (n + 1)
    · rw [hf1 (n + 1) hX]
      exact (hf01 n X).2
    · have : X ∉ tsupport (f n) := fun h => hX (hWL n (hfs n h))
      rw [image_eq_zero_of_notMem_tsupport this]
      exact (hf01 _ X).1
  have hmono' : ∀ X, Monotone fun n => f n X := fun X => monotone_nat_of_le_succ fun n => hmono n X
  have hmeas : ∀ n, Measurable fun X => ENNReal.ofReal (h X * f n X) := fun n =>
    ENNReal.measurable_ofReal.comp (hc.mul (f n).continuous).measurable
  have hsup : ∀ s, ∫⁻ X, ENNReal.ofReal (h X) ∂(m s) = ⨆ n, ∫⁻ X, ENNReal.ofReal (h X * f n X) ∂(m s) := by
    intro s
    rw [← lintegral_iSup hmeas]
    · have hae : ∀ᵐ X ∂(m s), X ∈ U := by
        rw [ae_iff]
        exact hnull s
      refine lintegral_congr_ae (hae.mono fun X hX => le_antisymm ?_ ?_)
      · have hm : X ∈ L (K.find ⟨X, hX⟩) := ⟨⟨X, hX⟩, K.mem_find _, rfl⟩
        refine le_iSup_of_le (K.find ⟨X, hX⟩) ?_
        rw [hf1 _ hm]
        simp
      · refine iSup_le fun n => ENNReal.ofReal_le_ofReal ?_
        exact mul_le_of_le_one_right (h0 X) (hf01 n X).2
    · intro a b hab X
      exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (hmono' X hab) (h0 X))
  have hn : ∀ n, Measurable (B.indicator fun s => ∫⁻ X, ENNReal.ofReal (h X * f n X) ∂(m s)) := by
    intro n
    have hcs : HasCompactSupport fun X => h X * f n X := HasCompactSupport.mul_left (hfc n)
    have hts : tsupport (fun X => h X * f n X) ⊆ U :=
      (tsupport_mul_subset_right (f := h) (g := f n)).trans ((hfs n).trans (hWU n))
    obtain ⟨i1, i2⟩ := h3 (fun X => h X * f n X) (hc.mul (f n).continuous) hcs hts
    have hm : Measurable (B.piecewise (fun s => ENNReal.ofReal (∫ X, h X * f n X ∂(m s))) fun _ => 0) :=
      ContinuousOn.measurable_piecewise (ENNReal.continuous_ofReal.comp_continuousOn i2) continuousOn_const
        hB.measurableSet
    convert hm using 1
    funext s
    by_cases hs : s ∈ B
    · rw [Set.indicator_of_mem hs, Set.piecewise_eq_of_mem _ _ _ hs,
        ofReal_integral_eq_lintegral_ofReal (i1 s hs)
          (Filter.Eventually.of_forall fun X => mul_nonneg (h0 X) (hf01 n X).1)]
    · rw [Set.indicator_of_notMem hs, Set.piecewise_eq_of_notMem _ _ _ hs]
  have : (B.indicator fun s => ∫⁻ X, ENNReal.ofReal (h X) ∂(m s)) =
      fun s => ⨆ n, B.indicator (fun s => ∫⁻ X, ENNReal.ofReal (h X * f n X) ∂(m s)) s := by
    funext s
    by_cases hs : s ∈ B
    · simp only [Set.indicator_of_mem hs, hsup]
    · simp only [Set.indicator_of_notMem hs, iSup_const]
  rw [this]
  exact Measurable.iSup hn

theorem fibre_cut_nonneg [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V]
    {μ : Measure V} {ν : Measure R} {q : V → R} {m : R → Measure V} {U : Set V} {B : Set R} (hU : IsOpen U)
    (hB : IsOpen B) (hf : IsFibreFamily μ q id U ν B m) (hq : Measurable q) (hqU : ∀ X, q X ∈ B → X ∈ U)
    {h : V → ℝ} (hc : Continuous h)
    (h0 : ∀ X, 0 ≤ h X) {ρ : R → ℝ} (hρc : Continuous ρ) (hρ0 : ∀ s, 0 ≤ ρ s) (hρB : tsupport ρ ⊆ B)
    (hfin : ∀ s ∈ tsupport ρ, Integrable h (m s)) (hμ : Integrable (fun X => h X * ρ (q X)) μ) :
    Integrable (fun s => ρ s * ∫ X, h X ∂(m s)) ν ∧
      ∫ X, h X * ρ (q X) ∂μ = ∫ s, ρ s * ∫ X, h X ∂(m s) ∂ν := by
  have hTm := measurable_fibre_lintegral hU hB hf hc h0
  obtain ⟨h1, h2, -⟩ := hf
  set T : R → ℝ≥0∞ := fun s => ∫⁻ X, ENNReal.ofReal (h X) ∂(m s) with hT
  have hint : ∀ s, ∫ X, h X ∂(m s) = (T s).toReal := fun s =>
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall h0) hc.aestronglyMeasurable
  have hhm : Measurable fun X => ENNReal.ofReal (h X) := ENNReal.measurable_ofReal.comp hc.measurable
  have key : ∫⁻ X, ENNReal.ofReal (h X * ρ (q X)) ∂μ = ∫⁻ s, ENNReal.ofReal (ρ s) * T s ∂ν := by
    have e := h2 (fun X => ENNReal.ofReal (h X * ρ (q X)))
      (ENNReal.measurable_ofReal.comp (hc.measurable.mul (hρc.measurable.comp hq)))
    have hz : ∫⁻ X in U, ENNReal.ofReal (h X * ρ (q X)) ∂μ = ∫⁻ X, ENNReal.ofReal (h X * ρ (q X)) ∂μ := by
      rw [← lintegral_indicator hU.measurableSet]
      refine lintegral_congr fun X => ?_
      by_cases hX : X ∈ U
      · rw [Set.indicator_of_mem hX]
      · have hn : q X ∉ tsupport ρ := fun hh => hX (hqU X (hρB hh))
        rw [Set.indicator_of_notMem hX, image_eq_zero_of_notMem_tsupport hn]
        simp
    rw [← hz, e]
    refine lintegral_congr fun s => ?_
    have hae : ∀ᵐ X ∂(m s), q X = s := by
      rw [ae_iff]
      refine measure_mono_null ?_ (h1 s)
      intro X hX hX'
      exact hX hX'.1
    calc ∫⁻ X, ENNReal.ofReal (h X * ρ (q X)) ∂(m s)
        = ∫⁻ X, ENNReal.ofReal (ρ s) * ENNReal.ofReal (h X) ∂(m s) :=
          lintegral_congr_ae (hae.mono fun X hX => by
            simp only [hX]
            rw [ENNReal.ofReal_mul (h0 X), mul_comm])
      _ = ENNReal.ofReal (ρ s) * T s := lintegral_const_mul _ hhm
  have hQ : ∀ s, ENNReal.ofReal (ρ s * ∫ X, h X ∂(m s)) = ENNReal.ofReal (ρ s) * T s := by
    intro s
    by_cases hs : s ∈ tsupport ρ
    · have hfinT : T s ≠ ∞ := ((hfin s hs).lintegral_lt_top).ne
      rw [ENNReal.ofReal_mul (hρ0 s), hint, ENNReal.ofReal_toReal hfinT]
    · simp [image_eq_zero_of_notMem_tsupport hs]
  have hnn : 0 ≤ᵐ[ν] fun s => ρ s * ∫ X, h X ∂(m s) :=
    Filter.Eventually.of_forall fun s => mul_nonneg (hρ0 s) (integral_nonneg h0)
  have hmeasQ : Measurable fun s => ρ s * ∫ X, h X ∂(m s) := by
    have : (fun s => ρ s * ∫ X, h X ∂(m s)) =
        fun s => ρ s * (B.indicator T s).toReal := by
      funext s
      by_cases hs : s ∈ B
      · rw [Set.indicator_of_mem hs, hint]
      · have : s ∉ tsupport ρ := fun h => hs (hρB h)
        simp [image_eq_zero_of_notMem_tsupport this]
    rw [this]
    exact hρc.measurable.mul hTm.ennreal_toReal
  have hnnμ : 0 ≤ᵐ[μ] fun X => h X * ρ (q X) :=
    Filter.Eventually.of_forall fun X => mul_nonneg (h0 X) (hρ0 _)
  have hlt : ∫⁻ s, ENNReal.ofReal (ρ s * ∫ X, h X ∂(m s)) ∂ν < ∞ := by
    simp only [hQ]
    rw [← key]
    exact hμ.lintegral_lt_top
  refine ⟨⟨hmeasQ.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal hnn).2 hlt⟩, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae hnnμ hμ.1, integral_eq_lintegral_of_nonneg_ae hnn hmeasQ.aestronglyMeasurable,
    key]
  simp only [hQ]

theorem fibre_cut_real [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V]
    {μ : Measure V} {ν : Measure R} {q : V → R} {m : R → Measure V} {U : Set V} {B : Set R} (hU : IsOpen U)
    (hB : IsOpen B) (hf : IsFibreFamily μ q id U ν B m) (hq : Measurable q) (hqU : ∀ X, q X ∈ B → X ∈ U)
    {h : V → ℝ} (hc : Continuous h)
    {ρ : R → ℝ} (hρc : Continuous ρ) (hρ0 : ∀ s, 0 ≤ ρ s) (hρB : tsupport ρ ⊆ B)
    (hfin : ∀ s ∈ tsupport ρ, Integrable h (m s)) (hμ : Integrable (fun X => h X * ρ (q X)) μ) :
    Integrable (fun s => ρ s * ∫ X, h X ∂(m s)) ν ∧
      ∫ X, h X * ρ (q X) ∂μ = ∫ s, ρ s * ∫ X, h X ∂(m s) ∂ν := by
  have hpc : Continuous fun X => max (h X) 0 := hc.max continuous_const
  have hnc : Continuous fun X => max (-h X) 0 := hc.neg.max continuous_const
  have hpμ : Integrable (fun X => max (h X) 0 * ρ (q X)) μ :=
    hμ.pos_part.congr (Filter.Eventually.of_forall fun X => by
      simp [max_mul_of_nonneg _ _ (hρ0 (q X))])
  have hnμ : Integrable (fun X => max (-h X) 0 * ρ (q X)) μ :=
    hμ.neg_part.congr (Filter.Eventually.of_forall fun X => by
      simp [max_mul_of_nonneg _ _ (hρ0 (q X))])
  obtain ⟨a1, a2⟩ := fibre_cut_nonneg hU hB hf hq hqU hpc (fun X => le_max_right _ _) hρc hρ0 hρB
    (fun s hs => (hfin s hs).pos_part) hpμ
  obtain ⟨b1, b2⟩ := fibre_cut_nonneg hU hB hf hq hqU hnc (fun X => le_max_right _ _) hρc hρ0 hρB
    (fun s hs => (hfin s hs).neg_part) hnμ
  have hsplit : ∀ x : ℝ, x = max x 0 - max (-x) 0 := by
    intro x
    rcases le_total x 0 with h | h
    · simp [h]
    · simp [h]
  have hs : (fun s => ρ s * ∫ X, h X ∂(m s)) =
      fun s => ρ s * (∫ X, max (h X) 0 ∂(m s)) - ρ s * ∫ X, max (-h X) 0 ∂(m s) := by
    funext s
    by_cases hs : s ∈ tsupport ρ
    · rw [← mul_sub, ← integral_sub (hfin s hs).pos_part (hfin s hs).neg_part]
      simp only [← hsplit]
    · simp [image_eq_zero_of_notMem_tsupport hs]
  rw [hs]
  refine ⟨a1.sub b1, ?_⟩
  rw [integral_sub a1 b1, ← a2, ← b2, ← integral_sub hpμ hnμ]
  refine integral_congr_ae (Filter.Eventually.of_forall fun X => ?_)
  show h X * ρ (q X) = max (h X) 0 * ρ (q X) - max (-h X) 0 * ρ (q X)
  rw [← sub_mul, ← hsplit]

theorem integral_eq_re_add_im {α : Type} [MeasurableSpace α] {μ : Measure α} {f : α → ℂ} (hf : Integrable f μ) :
    ∫ x, f x ∂μ = ((∫ x, (f x).re ∂μ : ℝ) : ℂ) + ((∫ x, (f x).im ∂μ : ℝ) : ℂ) * Complex.I :=
  (integral_re_add_im hf).symm

theorem fibre_cut [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V]
    {μ : Measure V} {ν : Measure R} {q : V → R} {m : R → Measure V} {U : Set V} {B : Set R} (hU : IsOpen U)
    (hB : IsOpen B) (hf : IsFibreFamily μ q id U ν B m) (hq : Measurable q) (hqU : ∀ X, q X ∈ B → X ∈ U)
    {φ : V → ℂ} (hc : Continuous φ)
    {ρ : R → ℝ} (hρc : Continuous ρ) (hρ0 : ∀ s, 0 ≤ ρ s) (hρB : tsupport ρ ⊆ B)
    (hfin : ∀ s ∈ tsupport ρ, Integrable φ (m s)) (hμ : Integrable (fun X => φ X * (ρ (q X) : ℂ)) μ) :
    Integrable (fun s => (ρ s : ℂ) * ∫ X, φ X ∂(m s)) ν ∧
      ∫ X, φ X * (ρ (q X) : ℂ) ∂μ = ∫ s, (ρ s : ℂ) * ∫ X, φ X ∂(m s) ∂ν := by
  have hre : Integrable (fun X => (φ X).re * ρ (q X)) μ :=
    hμ.re.congr (Filter.Eventually.of_forall fun X => by simp)
  have him : Integrable (fun X => (φ X).im * ρ (q X)) μ :=
    hμ.im.congr (Filter.Eventually.of_forall fun X => by simp)
  obtain ⟨a1, a2⟩ := fibre_cut_real hU hB hf hq hqU (Complex.continuous_re.comp hc) hρc hρ0 hρB
    (fun s hs => (hfin s hs).re) hre
  obtain ⟨b1, b2⟩ := fibre_cut_real hU hB hf hq hqU (Complex.continuous_im.comp hc) hρc hρ0 hρB
    (fun s hs => (hfin s hs).im) him
  simp only [Function.comp_apply] at a1 a2 b1 b2
  have hs : (fun s => (ρ s : ℂ) * ∫ X, φ X ∂(m s)) =
      fun s => ((ρ s * ∫ X, (φ X).re ∂(m s) : ℝ) : ℂ) +
        ((ρ s * ∫ X, (φ X).im ∂(m s) : ℝ) : ℂ) * Complex.I := by
    funext s
    by_cases hs : s ∈ tsupport ρ
    · rw [integral_eq_re_add_im (hfin s hs)]
      push_cast
      ring
    · simp [image_eq_zero_of_notMem_tsupport hs]
  have a1' : Integrable (fun s => ((ρ s * ∫ X, (φ X).re ∂(m s) : ℝ) : ℂ)) ν := a1.ofReal
  have b1' : Integrable (fun s => ((ρ s * ∫ X, (φ X).im ∂(m s) : ℝ) : ℂ) * Complex.I) ν :=
    b1.ofReal.mul_const _
  rw [hs]
  refine ⟨a1'.add b1', ?_⟩
  rw [integral_add a1' b1', integral_mul_const, integral_complex_ofReal, integral_complex_ofReal, ← a2, ← b2,
    integral_eq_re_add_im hμ]
  simp only [Complex.re_mul_ofReal, Complex.im_mul_ofReal]

end Abs

section Lim

variable {V R : Type} [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V]
  [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] [AddCommGroup R] [IsTopologicalAddGroup R]

theorem fibre_avg_tendsto [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V]
    {μ : Measure V} {ν : Measure R} [ν.IsNegInvariant] [ν.IsAddLeftInvariant] {q : V → R} {m : R → Measure V}
    {U : Set V} {B : Set R} (hU : IsOpen U) (hB : IsOpen B) (hf : IsFibreFamily μ q id U ν B m) (hq : Measurable q)
    (hqU : ∀ X, q X ∈ B → X ∈ U) {φ : V → ℂ}
    (hc : Continuous φ) {c : R} (hcB : c ∈ B) (hev : ∀ᶠ s in 𝓝 c, Integrable φ (m s))
    (hcont : ContinuousAt (fun s => ∫ X, φ X ∂(m s)) c) (ρ : ℕ → R → ℝ)
    (hρ : ∀ k, Continuous (ρ k) ∧ (∀ y, 0 ≤ ρ k y) ∧ 0 < ∫ y, ρ k y ∂ν)
    (hsm : Filter.Tendsto (fun k => tsupport (ρ k)) Filter.atTop (𝓝 (0 : R)).smallSets)
    (hμ : ∀ k, Integrable (fun X => φ X * (ρ k (c - q X) : ℂ)) μ) :
    Filter.Tendsto (fun k => (∫ X, φ X * (ρ k (c - q X) : ℂ) ∂μ) / ((∫ y, ρ k y ∂ν : ℝ) : ℂ)) Filter.atTop
      (𝓝 (∫ X, φ X ∂(m c))) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hclose : ∀ᶠ s in 𝓝 c, dist (∫ X, φ X ∂(m s)) (∫ X, φ X ∂(m c)) < ε / 2 :=
    Metric.tendsto_nhds.1 hcont _ (half_pos hε)
  have hV := hev.and (hclose.and (hB.mem_nhds hcB))
  have hsub : Filter.Tendsto (fun y : R => c - y) (𝓝 0) (𝓝 c) := by
    have hcs : Continuous fun y : R => c - y := continuous_const.sub continuous_id
    simpa using hcs.tendsto (0 : R)
  filter_upwards [Filter.tendsto_smallSets_iff.1 hsm _ (hsub hV)] with k hk
  obtain ⟨k1, k3, k4⟩ := hρ k
  have hrc : Continuous fun s => ρ k (c - s) := k1.comp (continuous_const.sub continuous_id)
  have hts : ∀ s ∈ tsupport (fun s => ρ k (c - s)), Integrable φ (m s) ∧
      dist (∫ X, φ X ∂(m s)) (∫ X, φ X ∂(m c)) < ε / 2 ∧ s ∈ B := by
    intro s hs
    have h1 := tsupport_comp_subset_preimage (ρ k) (f := fun s => c - s)
      (continuous_const.sub continuous_id) hs
    have h3 : Integrable φ (m (c - (c - s))) ∧
        dist (∫ X, φ X ∂(m (c - (c - s)))) (∫ X, φ X ∂(m c)) < ε / 2 ∧ c - (c - s) ∈ B := hk h1
    rwa [sub_sub_cancel] at h3
  obtain ⟨c1, c2⟩ := fibre_cut hU hB hf hq hqU hc hrc (fun s => k3 _) (fun s hs => (hts s hs).2.2)
    (fun s hs => (hts s hs).1) (hμ k)
  have hD : ∫ s, ρ k (c - s) ∂ν = ∫ y, ρ k y ∂ν := integral_sub_left_eq_self (ρ k) ν c
  have hρi : Integrable (ρ k) ν := by
    by_contra h
    rw [integral_undef h] at k4
    exact lt_irrefl _ k4
  have hri : Integrable (fun s => ρ k (c - s)) ν := hρi.comp_sub_left c
  set D : ℝ := ∫ y, ρ k y ∂ν with hDdef
  set G : R → ℂ := fun s => ∫ X, φ X ∂(m s) with hG
  have hriC : Integrable (fun s => ((ρ k (c - s) : ℝ) : ℂ) * G c) ν := (hri.ofReal).mul_const _
  have hdiff : (∫ X, φ X * (ρ k (c - q X) : ℂ) ∂μ) - (D : ℂ) * G c =
      ∫ s, ((ρ k (c - s) : ℝ) : ℂ) * (G s - G c) ∂ν := by
    simp only [mul_sub]
    rw [integral_sub c1 hriC, c2, integral_mul_const, integral_complex_ofReal, hD]
  have hbound : ‖∫ s, ((ρ k (c - s) : ℝ) : ℂ) * (G s - G c) ∂ν‖ ≤ D * (ε / 2) := by
    have e : D * (ε / 2) = ∫ s, ρ k (c - s) * (ε / 2) ∂ν := by
      rw [integral_mul_const, hD]
    rw [e]
    refine norm_integral_le_of_norm_le (hri.mul_const _) (Filter.Eventually.of_forall fun s => ?_)
    by_cases hs : s ∈ tsupport (fun s => ρ k (c - s))
    · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (k3 _)]
      refine mul_le_mul_of_nonneg_left ?_ (k3 _)
      have := (hts s hs).2.1
      rw [dist_eq_norm] at this
      exact this.le
    · have : ρ k (c - s) = 0 := image_eq_zero_of_notMem_tsupport (f := fun s => ρ k (c - s)) hs
      simp [this]
  have hDne : (D : ℂ) ≠ 0 := by
    exact_mod_cast k4.ne'
  rw [dist_eq_norm]
  have e2 : (∫ X, φ X * (ρ k (c - q X) : ℂ) ∂μ) / (D : ℂ) - G c =
      ((∫ X, φ X * (ρ k (c - q X) : ℂ) ∂μ) - (D : ℂ) * G c) / (D : ℂ) := by
    field_simp
  rw [e2, hdiff, norm_div, Complex.norm_real, Real.norm_of_nonneg k4.le, div_lt_iff₀ k4]
  nlinarith

end Lim

end GlobalTheory.CompanionTheory.SiegelND.Coef.AvgInf

theorem GlobalTheory.CompanionTheory.SiegelND.Coef.avgInfN_tendsto : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J) (n : ℕ), 2 * n < M → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (laminf : Measure (Ainf F)), GlobalTheory.CompanionTheory.SW.IsStdInf laminf → ∀ minf : HermR (Ainf F) σ n → Measure (Fin n → Fin M → Ainf F ⊗[F] E), GlobalTheory.CompanionTheory.SW.IsGramFib (Ainf F) σ J n (GlobalTheory.CompanionTheory.SW.coordW (Ainf F) b laminf n M) (GlobalTheory.CompanionTheory.SW.coordHerm (Ainf F) σ b laminf n) minf → ∀ c : HermR (Ainf F) σ n, IsUnit (c : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).det → ∀ φ : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ, IsSchwartzArch φ → ∀ ρ : ℕ → HermR (Ainf F) σ n → ℝ, (∀ k, Continuous (ρ k) ∧ HasCompactSupport (ρ k) ∧ (∀ y, 0 ≤ ρ k y) ∧ 0 < ∫ y, ρ k y ∂(GlobalTheory.CompanionTheory.SW.coordHerm (Ainf F) σ b laminf n)) → Filter.Tendsto (fun k => tsupport (ρ k)) Filter.atTop (nhds (0 : HermR (Ainf F) σ n)).smallSets → (∀ k, Measurable (fun X => φ X * (ρ k (c - gramH hCM hJ (Ainf F) X) : ℂ)) ∧ Integrable (fun X => φ X * (ρ k (c - gramH hCM hJ (Ainf F) X) : ℂ)) (GlobalTheory.CompanionTheory.SW.coordW (Ainf F) b laminf n M)) ∧ Filter.Tendsto (fun k => (∫ X, φ X * (ρ k (c - gramH hCM hJ (Ainf F) X) : ℂ) ∂(GlobalTheory.CompanionTheory.SW.coordW (Ainf F) b laminf n M)) / ((∫ y, ρ k y ∂(GlobalTheory.CompanionTheory.SW.coordHerm (Ainf F) σ b laminf n) : ℝ) : ℂ)) Filter.atTop (nhds (∫ X, φ X ∂(minf c))) := by
  intro F E _ _ _ _ _ σ hCM M J hJ n hM d b laminf hstd minf hm c hc φ hφ ρ hρ hsm
  have hLoc := GlobalTheory.CompanionTheory.SW.isLocR_Ainf F hCM.1
  obtain ⟨l1, l2, l3, l4, -, -, -, -⟩ := id hLoc
  haveI := l1
  haveI := l2
  haveI := l3
  haveI := l4
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  obtain ⟨t1, t2, t3, t4, -, -, -, t8, -, t10⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM (Ainf F)
  haveI := t1
  haveI := t2
  haveI := t3
  haveI := t4
  haveI := t8 n M
  obtain ⟨x1, x2, x3, x4, -⟩ := GlobalTheory.CompanionTheory.SW.HermTop.herm_top F E σ hCM (Ainf F) n
  haveI := x1
  haveI := x2
  haveI := x3
  haveI := x4
  haveI : LocallyCompactSpace (HermR (Ainf F) σ n) := x1
  haveI : SecondCountableTopology (HermR (Ainf F) σ n) := x2
  haveI : T2Space (HermR (Ainf F) σ n) := x3
  haveI : BorelSpace (HermR (Ainf F) σ n) := ⟨rfl⟩
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  obtain ⟨-, hW, hH⟩ := GlobalTheory.CompanionTheory.SW.coord_measures_haar F E σ hCM (Ainf F) d b laminf hstd.1
  set μ := GlobalTheory.CompanionTheory.SW.coordW (Ainf F) b laminf n M with hμdef
  let ν : Measure (HermR (Ainf F) σ n) := GlobalTheory.CompanionTheory.SW.coordHerm (Ainf F) σ b laminf n
  haveI hμH : μ.IsAddHaarMeasure := hW n M
  haveI hνH : ν.IsAddHaarMeasure := hH n
  haveI : ν.IsNegInvariant := Measure.IsAddHaarMeasure.isNegInvariant_of_regular ν
  have hqc : Continuous fun X : Fin n → Fin M → Ainf F ⊗[F] E => gramH hCM hJ (Ainf F) X :=
    (t10 n M J).subtype_mk _
  have hUo : IsOpen {X : Fin n → Fin M → Ainf F ⊗[F] E | IsUnit (gramR (Ainf F) σ J X).det} :=
    (PI.VolStabS.isOpen_isUnit_det (Ainf F) (PI.VolStabS.isOpen_units_Ainf F) n).preimage (t10 n M J)
  have hBo : IsOpen {S : HermR (Ainf F) σ n | IsUnit (S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).det} :=
    PI.VolStabS.isOpen_unitHerm (Ainf F) (PI.VolStabS.isOpen_units_Ainf F) σ n
  have hfam : IsFibreFamily μ (fun X => gramH hCM hJ (Ainf F) X) id
      {X | IsUnit (gramR (Ainf F) σ J X).det} ν
      {S | IsUnit (S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).det} minf := by
    obtain ⟨h1, h2, h3⟩ := hm
    refine ⟨fun s => ?_, h2, h3⟩
    refine measure_mono_null (Set.compl_subset_compl.2 ?_) (h1 s)
    rintro X ⟨hX, hU⟩
    exact ⟨Subtype.ext hX, hU⟩
  have hφc : Continuous φ := by
    obtain ⟨N, e, he, -, f, hf⟩ := hφ
    have : φ = fun X => f (e X) := funext hf
    rw [this]
    exact f.continuous.comp he
  have hφi : Integrable φ μ := by
    obtain ⟨N, e, he, he', f, hf⟩ := hφ
    have h1 : (μ.map e).IsAddHaarMeasure := AddEquiv.isAddHaarMeasure_map μ e he he'
    have h2 : Integrable f (μ.map e) := f.integrable
    have h3 := h2.comp_measurable he.measurable
    exact h3.congr (Filter.Eventually.of_forall fun X => (hf X).symm)
  have hcut : ∀ k, Continuous (fun X => φ X * (ρ k (c - gramH hCM hJ (Ainf F) X) : ℂ)) := fun k =>
    hφc.mul (Complex.continuous_ofReal.comp ((hρ k).1.comp (continuous_const.sub hqc)))
  have hint : ∀ k, Integrable (fun X => φ X * (ρ k (c - gramH hCM hJ (Ainf F) X) : ℂ)) μ := by
    intro k
    obtain ⟨C, hC⟩ := (hρ k).1.bounded_above_of_compact_support (hρ k).2.1
    refine (hφi.norm.mul_const C).mono' (hcut k).aestronglyMeasurable
      (Filter.Eventually.of_forall fun X => ?_)
    rw [norm_mul, Complex.norm_real]
    exact mul_le_mul_of_nonneg_left (hC _) (norm_nonneg _)
  obtain ⟨-, hev, hcont⟩ := GlobalTheory.T.archimedean_gram_fibre_measure_formula F E σ hCM M J hJ n hM d b laminf hstd minf hm c hc φ hφ
  refine ⟨fun k => ⟨(hcut k).measurable, hint k⟩, ?_⟩
  exact GlobalTheory.CompanionTheory.SiegelND.Coef.AvgInf.fibre_avg_tendsto (R := HermR (Ainf F) σ n) (ν := ν) hUo hBo hfam hqc.measurable
    (fun X hX => hX) hφc hc hev hcont ρ (fun k => ⟨(hρ k).1, (hρ k).2.2.1, (hρ k).2.2.2⟩) hsm hint
