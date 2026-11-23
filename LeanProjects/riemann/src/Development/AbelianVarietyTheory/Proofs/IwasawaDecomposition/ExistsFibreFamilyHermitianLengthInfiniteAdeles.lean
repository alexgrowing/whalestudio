import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousDistribHaarCharUnits
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsNiceLocalFieldProductRingInfiniteAdelesComplet
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HermitianFormFiniteZerosOnLineCmExt

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.GaugeEx.FibExist

section Generic

variable {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]

omit [TopologicalSpace R] [IsTopologicalRing R] in
theorem isUnit_of_mul_inverse {t a : R} (h : IsUnit (t * Ring.inverse a)) : IsUnit a := by
  by_contra ha
  rw [Ring.inverse_non_unit a ha, mul_zero, isUnit_zero_iff] at h
  haveI := subsingleton_of_zero_eq_one h
  exact ha (isUnit_of_subsingleton a)

omit [TopologicalSpace R] [IsTopologicalRing R] in
theorem isUnit_inv {a : R} (h : IsUnit a) : IsUnit (Ring.inverse a) :=
  IsUnit.of_mul_eq_one a (Ring.inverse_mul_cancel a h)

omit [IsTopologicalRing R] in
theorem isOpen_isUnit (h : IsOpenUnits R) : IsOpen {a : R | IsUnit a} :=
  h.isOpenEmbedding_unitsVal.isOpen_range

omit [IsTopologicalRing R] in
theorem continuousOn_inverse (h : IsOpenUnits R) :
    ContinuousOn (Ring.inverse : R → R) {a | IsUnit a} := by
  rintro _ ⟨u, rfl⟩
  refine ContinuousAt.continuousWithinAt ?_
  rw [← h.isOpenEmbedding_unitsVal.continuousAt_iff]
  have : (Ring.inverse : R → R) ∘ Units.val = fun u : Rˣ => ((u⁻¹ : Rˣ) : R) := by
    ext u; simp
  rw [this]
  exact Units.continuous_coe_inv.continuousAt

theorem exists_measurable_eqOn {X Y : Type} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y] (y : Y) {U : Set X} (hU : IsOpen U)
    {f : X → Y} (hf : ContinuousOn f U) :
    ∃ g : X → Y, Measurable g ∧ (∀ x ∈ U, g x = f x) ∧ ∀ x ∉ U, g x = y := by
  classical
  exact ⟨U.piecewise f fun _ => y,
    hf.measurable_piecewise continuousOn_const hU.measurableSet,
    fun x hx => Set.piecewise_eq_of_mem _ _ _ hx, fun x hx => Set.piecewise_eq_of_notMem _ _ _ hx⟩

variable [T2Space R] [LocallyCompactSpace R] [SecondCountableTopology R] [MeasurableSpace R]
  [BorelSpace R]

omit [IsTopologicalRing R] [T2Space R] [LocallyCompactSpace R] [SecondCountableTopology R] in
theorem measurable_inverse (h : IsOpenUnits R) : Measurable (Ring.inverse : R → R) := by
  obtain ⟨g, h1, h2, h3⟩ := exists_measurable_eqOn (0 : R) (isOpen_isUnit h) (continuousOn_inverse h)
  convert h1 using 1
  ext a
  by_cases ha : IsUnit a
  · exact (h2 a ha).symm
  · rw [h3 a ha, Ring.inverse_non_unit a ha]

variable {V : Type} [AddCommGroup V] [Module R V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [ContinuousSMul R V] [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V]
  [MeasurableSpace V] [BorelSpace V]

omit [IsTopologicalRing R] [T2Space R] [LocallyCompactSpace R] [SecondCountableTopology R]
  [MeasurableSpace R] [BorelSpace R] [T2Space V] in

theorem exists_map_smul (μ : Measure V) [μ.IsAddHaarMeasure] {c : R} (hc : IsUnit c) :
    ∃ d : ℝ≥0, d ≠ 0 ∧ μ.map (fun x : V => c • x) = d • μ := by
  let e : V ≃ₜ+ V :=
    { toFun := fun x => c • x
      invFun := fun x => Ring.inverse c • x
      left_inv := fun x => by simp [smul_smul, Ring.inverse_mul_cancel _ hc]
      right_inv := fun x => by simp [smul_smul, Ring.mul_inverse_cancel _ hc]
      map_add' := fun x y => smul_add c x y
      continuous_toFun := continuous_const_smul c
      continuous_invFun := continuous_const_smul _ }
  haveI : (μ.map (fun x : V => c • x)).IsAddHaarMeasure := e.isAddHaarMeasure_map μ
  exact ⟨_, (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ μ).ne',
    Measure.isAddLeftInvariant_eq_smul _ μ⟩

omit [IsTopologicalRing R] [T2Space R] [LocallyCompactSpace R] [SecondCountableTopology R]
  [MeasurableSpace R] [BorelSpace R] [IsTopologicalAddGroup V] [LocallyCompactSpace V]
  [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V] in

theorem exists_compact_pull (ho : IsOpenUnits R) {S : Set R} (hS : IsCompact S) {s : R → R}
    (hs : ContinuousOn s S) (hu : ∀ u ∈ S, IsUnit (s u)) {K : Set V} (hK : IsCompact K) :
    ∃ K' : Set V, IsCompact K' ∧ ∀ u ∈ S, ∀ x, s u • x ∈ K → x ∈ K' := by
  refine ⟨(fun p : R × V => p.1 • p.2) '' (((fun u => Ring.inverse (s u)) '' S) ×ˢ K),
    ((hS.image_of_continuousOn ((continuousOn_inverse ho).comp hs hu)).prod hK).image
      continuous_smul, fun u hu' x hx => ⟨(_, s u • x), ⟨⟨u, hu', rfl⟩, hx⟩, ?_⟩⟩
  show Ring.inverse (s u) • s u • x = x
  rw [smul_smul, Ring.inverse_mul_cancel _ (hu u hu'), one_smul]

omit [IsTopologicalRing R] [LocallyCompactSpace R] in

theorem exists_avg_const (ho : IsOpenUnits R) (μ : Measure V) [μ.IsAddHaarMeasure]
    (ν : Measure R) [ν.IsOpenPosMeasure] [IsFiniteMeasureOnCompacts ν]
    {S : Set R} (hS : IsCompact S) {s : R → R} (hsm : Measurable s)
    (hs : ContinuousOn s S) (hu : ∀ u ∈ S, IsUnit (s u)) {ψ : R → ℝ≥0} (hψ : Continuous ψ)
    (hψS : ∀ u, ψ u ≠ 0 → u ∈ S) (hψ1 : ∀ u, ψ u ≤ 1) (hψ0 : ψ 1 ≠ 0) :
    ∃ C : ℝ≥0∞, C ≠ 0 ∧ C ≠ ⊤ ∧ ∀ φ : V → ℝ≥0∞, Measurable φ →
      ∫⁻ u, ψ u * ∫⁻ x, φ (s u • x) ∂μ ∂ν = C * ∫⁻ x, φ x ∂μ := by
  obtain ⟨K, hK, hK0⟩ := exists_compact_mem_nhds (0 : V)
  have hKpos : μ K ≠ 0 := (Measure.measure_pos_of_mem_nhds μ hK0).ne'
  have hKfin : μ K ≠ ⊤ := hK.measure_lt_top.ne
  let D : R → ℝ≥0∞ := fun u => μ {x | s u • x ∈ K} / μ K
  have hDm : Measurable D := by
    have : MeasurableSet {p : R × V | s p.1 • p.2 ∈ K} :=
      ((hsm.comp measurable_fst).smul measurable_snd) hK.measurableSet
    exact (measurable_measure_prodMk_left (ν := μ) this).div_const _
  have hD : ∀ u ∈ S, D u ≠ 0 ∧ μ.map (fun x : V => s u • x) = D u • μ := by
    intro u hu'
    obtain ⟨d, hd, h⟩ := exists_map_smul μ (hu u hu')
    have h1 := Measure.map_apply (μ := μ) (continuous_const_smul (s u)).measurable hK.measurableSet
    rw [h] at h1
    have h2 : D u = d := by
      have h3 : μ {x | s u • x ∈ K} = d * μ K := by simpa [Set.preimage] using h1.symm
      simp only [D, h3]
      rw [ENNReal.mul_div_cancel_right hKpos hKfin]
    rw [h2, h]
    exact ⟨by exact_mod_cast hd, rfl⟩
  have hm : Measurable fun u => (ψ u : ℝ≥0∞) * D u := hψ.measurable.coe_nnreal_ennreal.mul hDm
  refine ⟨∫⁻ u, ψ u * D u ∂ν, ?_, ?_, fun φ hφ => ?_⟩
  · refine ((lintegral_pos_iff_support hm).2 ?_).ne'
    refine lt_of_lt_of_le ((isOpen_ne_fun hψ continuous_zero).measure_pos ν ⟨1, hψ0⟩)
      (measure_mono fun u hu' => mul_ne_zero (by exact_mod_cast hu') (hD u (hψS u hu')).1)
  · obtain ⟨K', hK', h⟩ := exists_compact_pull ho hS hs hu hK
    have : ∫⁻ u, ψ u * D u ∂ν ≤ ∫⁻ u, S.indicator (fun _ => μ K' / μ K) u ∂ν := by
      refine lintegral_mono fun u => ?_
      by_cases h0 : ψ u = 0
      · simp [h0]
      rw [Set.indicator_of_mem (hψS u h0), ← one_mul (μ K' / μ K)]
      refine mul_le_mul' (ENNReal.coe_le_one_iff.2 (hψ1 u)) ?_
      exact ENNReal.div_le_div_right (measure_mono fun x hx => h u (hψS u h0) x hx) _
    refine ne_top_of_le_ne_top ?_ this
    rw [lintegral_indicator_const hS.measurableSet]
    exact ENNReal.mul_ne_top (ENNReal.div_ne_top hK'.measure_lt_top.ne hKpos) hS.measure_lt_top.ne
  · rw [← lintegral_mul_const _ hm]
    refine lintegral_congr fun u => ?_
    by_cases h0 : ψ u = 0
    · simp [h0]
    rw [← lintegral_map hφ (continuous_const_smul (s u)).measurable, (hD u (hψS u h0)).2,
      lintegral_smul_measure, smul_eq_mul, mul_assoc]

theorem exists_fibreFamily (hR : Nice R) (μ : Measure V) [μ.IsAddHaarMeasure]
    (ν : Measure R) [hν : ν.IsAddHaarMeasure] (q : V → R) (hq : Continuous q)
    (hq2 : ∀ (c : R) (x : V), q (c • x) = c ^ 2 * q x) (h0 : ∀ᵐ x ∂μ, IsUnit (q x)) :
    ∃ fib : R → Measure V, IsFibreFamily μ q id Set.univ ν {c | IsUnit c} fib := by
  obtain ⟨-, -, ho, U₀, hU₀, h1, s₀, hs₀, -, hss₀⟩ := hR
  have hUn := isOpen_isUnit ho
  have hic := continuousOn_inverse ho
  have him := measurable_inverse ho
  obtain ⟨hm1, -, -, hm4⟩ := modu_basic R

  obtain ⟨U, hU, h1U, hUu, s, hsm, hs, hss⟩ : ∃ U : Set R, IsOpen U ∧ (1 : R) ∈ U ∧
      (∀ u ∈ U, IsUnit u) ∧ ∃ s : R → R, Measurable s ∧ ContinuousOn s U ∧
      ∀ u ∈ U, s u ^ 2 = u := by
    obtain ⟨s, hsm, hs, -⟩ := exists_measurable_eqOn (0 : R) hU₀ hs₀
    refine ⟨U₀ ∩ {a | IsUnit a}, hU₀.inter hUn, ⟨h1, isUnit_one⟩, fun u hu => hu.2, s, hsm,
      (hs₀.congr hs).mono Set.inter_subset_left, fun u hu => ?_⟩
    rw [hs u hu.1, sq, hss₀ u hu.1]
  obtain ⟨S, hS, h1S, hSU⟩ := exists_compact_subset hU h1U
  have hsu : ∀ u ∈ S, IsUnit (s u) := fun u hu =>
    (isUnit_pow_iff two_ne_zero).1 (by rw [hss u (hSU hu)]; exact hUu u (hSU hu))

  obtain ⟨ψ, hψ, hψS, hψ1, hψ0⟩ : ∃ ψ : R → ℝ≥0, Continuous ψ ∧ (∀ u, ψ u ≠ 0 → u ∈ S) ∧
      (∀ u, ψ u ≤ 1) ∧ ψ 1 ≠ 0 := by
    obtain ⟨f, f1, f0, -, f01⟩ := exists_continuous_one_zero_of_isCompact
      (isCompact_singleton (x := (1 : R))) (isOpen_interior (s := S)).isClosed_compl
      (Set.disjoint_singleton_left.2 fun h => h h1S)
    refine ⟨fun u => (f u).toNNReal, continuous_real_toNNReal.comp f.continuous, fun u hu => ?_,
      fun u => Real.toNNReal_le_one.2 (f01 u).2, ?_⟩
    · by_contra h
      exact hu (by show (f u).toNNReal = 0; rw [f0 (fun h' => h (interior_subset h'))]; simp)
    · show (f 1).toNNReal ≠ 0
      rw [f1 rfl]; simp

  have hωc : ContinuousOn (fun a : R => modu R (Ring.inverse a)) {a | IsUnit a} :=
    (hm4 ho).comp hic fun a ha => isUnit_inv ha
  obtain ⟨ω, hωm, hω, -⟩ := exists_measurable_eqOn (0 : ℝ≥0) hUn hωc
  have hωc' : ContinuousOn ω {a | IsUnit a} := hωc.congr hω
  obtain ⟨C, hC0, hCt, hC⟩ := exists_avg_const ho μ ν hS hsm (hs.mono hSU) hsu hψ hψS hψ1 hψ0
  let r : R → V → R := fun t x => t * Ring.inverse (q x)
  have hrm : Measurable fun p : R × V => r p.1 p.2 :=
    measurable_fst.mul (him.comp (hq.measurable.comp measurable_snd))
  let k : R → V → ℝ≥0 := fun t x => ψ (r t x) * ω (q x)
  have hkm : Measurable fun p : R × V => k p.1 p.2 :=
    (hψ.measurable.comp hrm).mul (hωm.comp (hq.measurable.comp measurable_snd))
  let g : R → V → V := fun t x => s (r t x) • x
  have hgm : Measurable fun p : R × V => g p.1 p.2 := (hsm.comp hrm).smul measurable_snd
  have hkt : ∀ t, Measurable (k t) := fun t => hkm.comp measurable_prodMk_left
  have hgt : ∀ t, Measurable (g t) := fun t => hgm.comp measurable_prodMk_left
  have hkS : ∀ t x, k t x ≠ 0 → r t x ∈ S := fun t x h => hψS _ (left_ne_zero_of_mul h)
  have hqu : ∀ t x, r t x ∈ S → IsUnit (q x) := fun t x h => isUnit_of_mul_inverse (hUu _ (hSU h))
  have hrq : ∀ t x, r t x ∈ S → r t x * q x = t := fun t x h => by
    simp only [r]
    rw [mul_assoc, Ring.inverse_mul_cancel _ (hqu t x h), mul_one]
  refine ⟨fun t => C⁻¹ • (μ.withDensity fun x => k t x).map (g t), fun t => ?_, fun φ hφ => ?_,
    fun φ hφ hc _ => ?_⟩
  · have hA : MeasurableSet (q ⁻¹' {id t} ∩ Set.univ)ᶜ :=
      (((isClosed_singleton.preimage hq).measurableSet).inter MeasurableSet.univ).compl
    rw [Measure.smul_apply, Measure.map_apply (hgt t) hA, withDensity_apply _ (hgt t hA),
      setLIntegral_congr_fun (g := fun _ => 0) (hgt t hA), lintegral_zero, smul_zero]
    intro x hx
    by_contra h
    have h' := hkS t x (fun h2 => h (by simp [h2]))
    refine hx ⟨?_, trivial⟩
    show q (s (r t x) • x) = t
    rw [hq2, hss _ (hSU h'), hrq t x h']
  · have hj : Measurable fun p : R × V => (k p.1 p.2 : ℝ≥0∞) * φ (g p.1 p.2) :=
      hkm.coe_nnreal_ennreal.mul (hφ.comp hgm)
    have inner : ∀ t, ∫⁻ v, φ v ∂(C⁻¹ • (μ.withDensity fun x => k t x).map (g t)) =
        C⁻¹ * ∫⁻ x, k t x * φ (g t x) ∂μ := fun t => by
      rw [lintegral_smul_measure, lintegral_map hφ (hgt t), smul_eq_mul]
      exact congrArg _
        (lintegral_withDensity_eq_lintegral_mul _ (hkt t).coe_nnreal_ennreal (hφ.comp (hgt t)))
    simp only [inner]
    have hj2 : Measurable fun p : V × R => (ψ p.2 : ℝ≥0∞) * φ (s p.2 • p.1) :=
      (hψ.measurable.comp measurable_snd).coe_nnreal_ennreal.mul
        (hφ.comp ((hsm.comp measurable_snd).smul measurable_fst))
    have step : ∀ᵐ x ∂μ, ∫⁻ t, k t x * φ (g t x) ∂ν = ∫⁻ u, ψ u * φ (s u • x) ∂ν := by
      filter_upwards [h0] with x hx
      have hgx : Measurable fun u => (ψ u : ℝ≥0∞) * φ (s u • x) := hj2.comp measurable_prodMk_left
      have hmul : Measurable fun z : R => Ring.inverse (q x) * z := measurable_const.mul measurable_id
      conv_rhs => rw [(hm1 _ (isUnit_inv hx)).2 ν hν]
      rw [lintegral_smul_measure, lintegral_map hgx hmul, ← hω _ hx, ENNReal.smul_def, smul_eq_mul,
        ← lintegral_const_mul' _ _ ENNReal.coe_ne_top]
      refine lintegral_congr fun t => ?_
      simp only [k, g, r, mul_comm t, ENNReal.coe_mul]
      ring
    rw [Measure.restrict_univ, lintegral_const_mul _ hj.lintegral_prod_right',
      lintegral_lintegral_swap hj.aemeasurable, lintegral_congr_ae step,
      lintegral_lintegral_swap hj2.aemeasurable]
    have e : ∀ u, ∫⁻ x, ψ u * φ (s u • x) ∂μ = ψ u * ∫⁻ x, φ (s u • x) ∂μ := fun u =>
      lintegral_const_mul _ (hφ.comp (continuous_const_smul (s u)).measurable)
    simp only [e]
    rw [hC φ hφ, ← mul_assoc, ENNReal.inv_mul_cancel hC0 hCt, one_mul]
  · obtain ⟨K, hK, hKp⟩ := exists_compact_pull ho hS (hs.mono hSU) hsu hc.isCompact
    obtain ⟨c, hcb⟩ := hφ.bounded_above_of_compact_support hc
    have hFm : ∀ t, AEStronglyMeasurable (fun x => k t x • φ (g t x)) μ := fun t =>
      ((hkt t).coe_nnreal_real.mul (hφ.measurable.comp (hgt t))).aestronglyMeasurable
    have hbound : ∀ T : Set R, IsCompact T → T ⊆ {a | IsUnit a} →
        ∃ b : V → ℝ, Integrable b μ ∧ ∀ t ∈ T, ∀ x, ‖k t x • φ (g t x)‖ ≤ b x := by
      intro T hT hTu
      have hA : IsCompact ((fun p : R × R => p.1 * p.2) '' ((Ring.inverse '' S) ×ˢ T)) :=
        ((hS.image_of_continuousOn (hic.mono fun u hu => hUu u (hSU hu))).prod hT).image
          continuous_mul
      obtain ⟨B, hB⟩ := (hA.image_of_continuousOn (hωc'.mono (by
        rintro _ ⟨⟨_, t⟩, ⟨⟨u, hu, rfl⟩, ht⟩, rfl⟩
        exact (isUnit_inv (hUu u (hSU hu))).mul (hTu ht)))).bddAbove
      have hc0 : 0 ≤ c := (norm_nonneg _).trans (hcb 0)
      refine ⟨K.indicator fun _ => B * c, ?_, fun t ht x => ?_⟩
      · rw [integrable_indicator_iff hK.measurableSet]
        exact integrableOn_const hK.measure_lt_top.ne
      by_cases hk : k t x = 0
      · rw [hk, zero_smul, norm_zero]
        exact Set.indicator_nonneg (fun _ _ => by positivity) x
      have h' := hkS t x hk
      by_cases hx : x ∈ K
      · rw [Set.indicator_of_mem hx, NNReal.smul_def, smul_eq_mul, norm_mul]
        refine mul_le_mul ?_ (hcb _) (norm_nonneg _) B.coe_nonneg
        have hωB : ω (q x) ≤ B := by
          refine hB ⟨_, ⟨(Ring.inverse (r t x), t), ⟨⟨_, h', rfl⟩, ht⟩, ?_⟩, rfl⟩
          show Ring.inverse (r t x) * t = q x
          nth_rewrite 2 [← hrq t x h']
          rw [← mul_assoc, Ring.inverse_mul_cancel _ (hUu _ (hSU h')), one_mul]
        rw [NNReal.norm_eq, NNReal.coe_le_coe, ← one_mul B]
        exact mul_le_mul' (hψ1 _) hωB
      · rw [Set.indicator_of_notMem hx,
          image_eq_zero_of_notMem_tsupport (f := φ) (fun h => hx (hKp _ h' x h))]
        simp
    refine ⟨fun t ht => ?_, fun t₀ ht₀ => ?_⟩
    · refine Integrable.smul_measure ?_ (ENNReal.inv_ne_top.2 hC0)
      rw [integrable_map_measure hφ.aestronglyMeasurable (hgt t).aemeasurable,
        integrable_withDensity_iff_integrable_smul (hkt t)]
      obtain ⟨b, hb, hb'⟩ := hbound {t} isCompact_singleton (Set.singleton_subset_iff.2 ht)
      exact Integrable.mono' hb (hFm t) (Filter.Eventually.of_forall (hb' t rfl))
    · have e : ∀ t, ∫ v, φ v ∂(C⁻¹ • (μ.withDensity fun x => k t x).map (g t)) =
          C⁻¹.toReal * ∫ x, k t x • φ (g t x) ∂μ := fun t => by
        rw [integral_smul_measure, integral_map (hgt t).aemeasurable hφ.aestronglyMeasurable,
          integral_withDensity_eq_integral_smul (hkt t), smul_eq_mul]
      simp only [e]
      obtain ⟨T, hT, htT, hTu⟩ := exists_compact_subset hUn ht₀
      obtain ⟨b, hb, hb'⟩ := hbound T hT hTu
      refine (ContinuousAt.const_mul ?_ _).continuousWithinAt
      refine continuousAt_of_dominated (bound := b) (Filter.Eventually.of_forall hFm) ?_ hb ?_
      · filter_upwards [mem_interior_iff_mem_nhds.1 htT] with t ht
        exact Filter.Eventually.of_forall (hb' t ht)
      · refine Filter.Eventually.of_forall fun x => ?_
        have hcu : Continuous fun u : R => ((ψ u * ω (q x) : ℝ≥0) : ℝ) * φ (s u • x) := by
          refine ContinuousOn.continuous_of_tsupport_subset (s := U) ?_ hU ?_
          · exact (NNReal.continuous_coe.comp (hψ.mul continuous_const)).continuousOn.mul
              (hφ.comp_continuousOn (hs.smul continuousOn_const))
          · refine Set.Subset.trans (closure_minimal (fun u hu => hψS u fun h => ?_) hS.isClosed) hSU
            exact (Function.mem_support.1 hu) (by simp [h])
        exact (hcu.comp (continuous_id.mul continuous_const)).continuousAt

omit [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] [LocallyCompactSpace R]
  [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R] [ContinuousSMul R V] [T2Space V] in

theorem null_of_finite_curve (μ : Measure V) [μ.IsAddHaarMeasure] {Z : Set V} (hZ : MeasurableSet Z)
    {L : ℝ → V} (hL : Continuous L) (h : ∀ x : V, {t : ℝ | x + L t ∈ Z}.Finite) : μ Z = 0 := by
  have hc : Continuous (fun p : V × ℝ => p.1 + L p.2) := by fun_prop
  have hS : MeasurableSet {p : V × ℝ | p.1 + L p.2 ∈ Z} := hc.measurable hZ
  have h1 : (μ.prod volume) {p : V × ℝ | p.1 + L p.2 ∈ Z} = 0 := by
    rw [Measure.measure_prod_null hS]
    exact Filter.Eventually.of_forall fun x => (h x).measure_zero volume
  rw [Measure.prod_apply_symm hS] at h1
  have h2 : ∀ t : ℝ, μ ((fun x => (x, t)) ⁻¹' {p : V × ℝ | p.1 + L p.2 ∈ Z}) = μ Z :=
    fun t => measure_preimage_add_right μ (L t) Z
  simpa only [h2, lintegral_const, mul_eq_zero, Real.volume_univ, ENNReal.top_ne_zero, or_false]
    using h1

end Generic

section Herm

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)

theorem continuous_qR [TopologicalSpace R] [IsTopologicalRing R] :
    Continuous fun X : Fin 1 → Fin M → R ⊗[F] E => qR R σ J (X 0) := by
  have h1 : Continuous (Algebra.trace R (R ⊗[F] E)) := IsModuleTopology.continuous_of_linearMap _
  have h2 := GlobalTheory.AdelicUnitaryTop.continuous_sigR R σ
  unfold qR hR Formalism.UG.hform
  refine continuous_const.mul (h1.comp ?_)
  fun_prop

omit [NumberField F] [NumberField E] in
theorem qR_smul (c : R) (X : Fin 1 → Fin M → R ⊗[F] E) :
    qR R σ J ((c • X) 0) = c ^ 2 * qR R σ J (X 0) := by
  have h : ∀ z : R ⊗[F] E, sigR R σ (c • z) = c • sigR R σ z := fun z =>
    (Algebra.TensorProduct.map (AlgHom.id R R) σ).toLinearMap.map_smul c z
  have h2 : hR R σ J ((c • X) 0) ((c • X) 0) = c ^ 2 • hR R σ J (X 0) (X 0) := by
    simp only [hR, Formalism.UG.hform, Pi.smul_apply, h, Finset.smul_sum, smul_mul_assoc, mul_smul_comm,
      smul_smul, sq]
  unfold qR
  rw [h2, map_smul, smul_eq_mul]
  ring

theorem exists_line [Nontrivial R] (h : IsCMExt F E σ) (hM : 1 ≤ M) (hJ : IsHermND σ J) :
    ∃ (y : Fin M → R ⊗[F] E) (a : F), a ≠ 0 ∧ ∀ x : Fin M → R ⊗[F] E, ∃ c : R, ∀ t : R,
      qR R σ J (x + t • y) = algebraMap F R a * t ^ 2 + c * t + qR R σ J x := by
  obtain ⟨y0, a, ha, hy0⟩ := GlobalTheory.HermLineZeros.exists_anisotropic h hM hJ
  let y : Fin M → R ⊗[F] E := fun i => inclR R (y0 i)
  have hs : ∀ e : E, sigR R σ (inclR R e) = inclR R (σ e) := fun e => rfl
  have hyy : hR R σ J y y = algebraMap R (R ⊗[F] E) (algebraMap F R a) := by
    have : hR R σ J y y = inclR R (hE σ J y0 y0) := by
      simp only [hR, hE, Formalism.UG.hform, map_sum, map_mul, y, hs, JR, Matrix.map_apply,
        RingHom.coe_coe]
    rw [this, hy0, ← IsScalarTower.algebraMap_apply]
    exact (Algebra.TensorProduct.includeRight : E →ₐ[F] R ⊗[F] E).commutes a
  have hrk : Module.finrank R (R ⊗[F] E) = 2 := by
    rw [Module.finrank_baseChange, h.2.2.1]
  have hq : qR R σ J y = algebraMap F R a := by
    rw [qR, hyy, Algebra.trace_algebraMap, hrk, ← map_nsmul, ← map_mul]
    congr 1
    rw [nsmul_eq_mul]
    push_cast
    ring
  have hst : ∀ t : R, sigR R σ (algebraMap R (R ⊗[F] E) t) = algebraMap R (R ⊗[F] E) t := by
    intro t
    show t ⊗ₜ[F] σ 1 = _
    rw [map_one]
    rfl
  refine ⟨y, a, ha, fun x => ⟨algebraMap F R (1 / 2) *
    Algebra.trace R (R ⊗[F] E) (hR R σ J x y + hR R σ J y x), fun t => ?_⟩⟩
  have e : t • y = algebraMap R (R ⊗[F] E) t • y := by
    rw [algebraMap_smul]
  rw [← hq]
  unfold qR hR
  generalize algebraMap F R (1 / 2) = u
  rw [e, GlobalTheory.HermLineZeros.hform_expand, hst, mul_assoc (algebraMap R (R ⊗[F] E) t)]
  simp only [← Algebra.smul_def, map_add, map_smul, smul_eq_mul]
  ring

end Herm

theorem finite_quadratic_zeros {K : Type} [Field K] {a : K} (ha : a ≠ 0) (c d : K) :
    {t : K | a * t ^ 2 + c * t + d = 0}.Finite := by
  have hne : (Polynomial.C a * Polynomial.X ^ 2 + Polynomial.C c * Polynomial.X
      + Polynomial.C d : Polynomial K) ≠ 0 := by
    intro h0
    have := congrArg (fun p => Polynomial.coeff p 2) h0
    simp [Polynomial.coeff_X, Polynomial.coeff_C] at this
    exact ha this
  refine (Polynomial.finite_setOf_isRoot hne).subset fun t ht => ?_
  simpa [Polynomial.IsRoot] using ht

theorem isUnit_ainf_iff {F : Type} [Field F] [NumberField F] (c : Ainf F) :
    IsUnit c ↔ ∀ w, c w ≠ 0 := by
  have := Pi.isUnit_iff (x := (c : ∀ w : InfinitePlace F, w.Completion))
  simp only [isUnit_iff_ne_zero] at this
  exact this

theorem exists_fibreFamily_ainf : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (μ : Measure (Fin 1 → Fin M → Ainf F ⊗[F] E)) (ν : Measure (Ainf F)), 1 ≤ M → IsHermND σ J → μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → ∃ fib : Ainf F → Measure (Fin 1 → Fin M → Ainf F ⊗[F] E), IsFibreFamily μ (fun X => qR (Ainf F) σ J (X 0)) id Set.univ ν {c : Ainf F | ∀ w, c w ≠ 0} fib := by
  intro F E _ _ _ _ _ σ hσ M J μ ν hM hJ hμ hν
  classical
  have hq := continuous_qR (Ainf F) σ J
  have e : {c : Ainf F | ∀ w, c w ≠ 0} = {c | IsUnit c} := by
    ext c; exact (isUnit_ainf_iff c).symm
  rw [e]
  refine exists_fibreFamily (nice_ainf_fv F).1 μ ν _ hq (qR_smul _ σ J) ?_
  simp only [isUnit_ainf_iff]
  refine ae_all_iff.2 fun w => ?_
  haveI := hσ.1
  have hw : w.IsReal := IsTotallyReal.isReal w
  obtain ⟨y, a, ha, hy⟩ := exists_line (Ainf F) σ J hσ hM hJ
  let i := (InfinitePlace.Completion.isometryEquivRealOfIsReal hw).symm
  let j : ℝ → Ainf F := fun t => Pi.single (M := fun w : InfinitePlace F => w.Completion) w (i t)
  have hj : Continuous j := (continuous_single (A := fun w : InfinitePlace F => w.Completion) w).comp
    i.continuous
  have hev : Continuous fun c : Ainf F => c w := continuous_apply w
  rw [ae_iff]
  simp only [ne_eq, not_not]
  refine null_of_finite_curve μ (isClosed_eq (hev.comp hq) continuous_const).measurableSet
    (L := fun t => j t • fun _ => y) (hj.smul continuous_const) fun x => ?_
  obtain ⟨c, hc⟩ := hy (x 0)
  have ha' : algebraMap F w.Completion a ≠ 0 := (map_ne_zero _).2 ha
  refine ((finite_quadratic_zeros ha' (c w) (qR (Ainf F) σ J (x 0) w)).preimage
    i.injective.injOn).subset fun t ht => ?_
  have h1 : qR (Ainf F) σ J (x 0 + j t • y) w = 0 := ht
  rw [hc] at h1
  have h2 : j t w = i t := Pi.single_eq_same _ _
  rw [Set.mem_preimage, Set.mem_setOf_eq, ← h2]
  exact h1

end GlobalTheory.GaugeEx.FibExist
