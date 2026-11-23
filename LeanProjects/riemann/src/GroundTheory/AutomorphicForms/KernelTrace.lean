import Mathlib
import GroundTheory.AutomorphicForms.TraceStrongLimit
import GroundTheory.AutomorphicForms.FinePartition
import GroundTheory.AutomorphicForms.HilbertSchmidtKernel

namespace GroundTheory.Automorphic

open MeasureTheory Filter Topology Uniformity Set
open scoped InnerProductSpace ENNReal ComplexConjugate NNReal

noncomputable section

section Kernel

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [MeasurableSpace X]
  [BorelSpace X]

theorem measurable_of_continuous_compactProd {Y β : Type*} [TopologicalSpace Y] [CompactSpace Y]
    [T2Space Y] [MeasurableSpace Y] [BorelSpace Y] [PseudoMetricSpace β] [MeasurableSpace β]
    [BorelSpace β] {k : X × Y → β} (hk : Continuous k) : Measurable k := by
  let : UniformSpace X := uniformSpaceOfCompactR1
  let : UniformSpace Y := uniformSpaceOfCompactR1
  exact measurable_of_continuous_prod hk

variable (μ : Measure X) [IsFiniteMeasure μ]

theorem memLp_contKernel (k : C(X × X, ℂ)) : MemLp k 2 (μ.prod μ) :=
  MemLp.of_bound (measurable_of_continuous_compactProd k.continuous).aestronglyMeasurable ‖k‖
    (ae_of_all _ fun z => k.norm_coe_le_norm z)

def contKernelOp (k : C(X × X, ℂ)) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  L2Kernel.kernelOp ((memLp_contKernel μ k).toLp k)

theorem contKernelOp_apply_ae (k : C(X × X, ℂ)) (f : Lp ℂ 2 μ) :
    contKernelOp μ k f =ᵐ[μ] fun x => ∫ y, k (x, y) * f y ∂μ :=
  L2Kernel.kernelOp_toLp_apply_ae (memLp_contKernel μ k) f

end Kernel

theorem Lp.coeFn_finsetSum {α E ι : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] {p : ℝ≥0∞} (s : Finset ι) (F : ι → Lp E p μ) :
    ⇑(∑ i ∈ s, F i) =ᵐ[μ] fun x => ∑ i ∈ s, F i x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    filter_upwards [Lp.coeFn_zero E p μ] with x hx
    simp only [Finset.sum_empty]
    exact hx
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    filter_upwards [Lp.coeFn_add (F a) (∑ i ∈ s, F i), ih] with x h1 h2
    rw [h1, Pi.add_apply, h2]

section Averaging

variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]

namespace MeasurablePartition

variable (p : MeasurablePartition X)

def nonnull : Finset ℕ := (Finset.range p.n).filter fun i => μ (p.E i) ≠ 0

variable {μ p} in
theorem measureReal_pos (i : p.nonnull μ) : 0 < μ.real (p.E i) := by
  have h := (Finset.mem_filter.1 i.2).2
  exact ENNReal.toReal_pos h (measure_ne_top μ _)

def avgVec (i : p.nonnull μ) : Lp ℂ 2 μ :=
  (((Real.sqrt (μ.real (p.E i)))⁻¹ : ℝ) : ℂ) •
    indicatorConstLp 2 (p.measurableSet i) (measure_ne_top μ _) (1 : ℂ)

def avgProj : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ := finProj (p.avgVec μ)

theorem inner_avgVec (i : p.nonnull μ) (f : Lp ℂ 2 μ) :
    ⟪p.avgVec μ i, f⟫_ℂ = (((Real.sqrt (μ.real (p.E i)))⁻¹ : ℝ) : ℂ) * ∫ x in p.E i, f x ∂μ := by
  rw [avgVec, inner_smul_left, L2.inner_indicatorConstLp_one, Complex.conj_ofReal]

theorem orthonormal_avgVec : Orthonormal ℂ (p.avgVec μ) := by
  classical
  rw [orthonormal_iff_ite]
  intro i j
  rw [avgVec, avgVec, inner_smul_left, inner_smul_right, Complex.conj_ofReal,
    L2.inner_indicatorConstLp_indicatorConstLp]
  split_ifs with h
  · subst h
    have hm := measureReal_pos i
    rw [Set.inter_self]
    simp only [inner_self_eq_norm_sq_to_K, norm_one, one_pow, RCLike.ofReal_one, mul_one,
      Complex.real_smul]
    have hr : (Real.sqrt (μ.real (p.E i)))⁻¹ * ((Real.sqrt (μ.real (p.E i)))⁻¹ *
        μ.real (p.E i)) = 1 := by
      rw [← mul_assoc, ← mul_inv, Real.mul_self_sqrt hm.le, inv_mul_cancel₀ hm.ne']
    exact_mod_cast hr
  · have hij : (i : ℕ) ≠ j := fun h' => h (Subtype.ext h')
    rw [(p.disjoint hij).inter_eq]
    simp

end MeasurablePartition

end Averaging

section Diagonal

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [MeasurableSpace X]
  [BorelSpace X] (μ : Measure X) [IsFiniteMeasure μ]

omit [T2Space X] in
theorem integrable_of_continuous_compact {f : X → ℂ} (hf : Continuous f) (ν : Measure X)
    [IsFiniteMeasure ν] : Integrable f ν := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hf.continuousOn
  exact Integrable.of_bound hf.aestronglyMeasurable C (ae_of_all _ fun x => hC x (mem_univ x))

namespace MeasurablePartition

variable (p : MeasurablePartition X)

omit [TopologicalSpace X] [CompactSpace X] [T2Space X] [BorelSpace X] in
theorem coeFn_avgVec (i : p.nonnull μ) :
    p.avgVec μ i =ᵐ[μ] fun y => (((Real.sqrt (μ.real (p.E i)))⁻¹ : ℝ) : ℂ) *
      (p.E i).indicator (fun _ => (1 : ℂ)) y := by
  filter_upwards [Lp.coeFn_smul (((Real.sqrt (μ.real (p.E i)))⁻¹ : ℝ) : ℂ)
    (indicatorConstLp 2 (p.measurableSet i) (measure_ne_top μ _) (1 : ℂ)),
    indicatorConstLp_coeFn (p := 2) (μ := μ) (hs := p.measurableSet i)
      (hμs := measure_ne_top μ _) (c := (1 : ℂ))] with y h1 h2
  rw [avgVec, h1, Pi.smul_apply, h2, smul_eq_mul]

theorem inner_avgVec_contKernelOp (k : C(X × X, ℂ)) (i : p.nonnull μ) :
    ⟪p.avgVec μ i, contKernelOp μ k (p.avgVec μ i)⟫_ℂ =
      (((μ.real (p.E i))⁻¹ : ℝ) : ℂ) * ∫ x in p.E i, ∫ y in p.E i, k (x, y) ∂μ ∂μ := by
  set r : ℂ := (((Real.sqrt (μ.real (p.E i)))⁻¹ : ℝ) : ℂ) with hr
  have h1 : contKernelOp μ k (p.avgVec μ i) =ᵐ[μ] fun x => r * ∫ y in p.E i, k (x, y) ∂μ := by
    filter_upwards [contKernelOp_apply_ae μ k (p.avgVec μ i)] with x hx
    rw [hx, ← integral_indicator (p.measurableSet i), ← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [coeFn_avgVec μ p i] with y hy
    rw [hy]
    by_cases hyE : y ∈ p.E i
    · rw [Set.indicator_of_mem hyE, Set.indicator_of_mem hyE, hr, mul_one]
      ring
    · simp [Set.indicator_of_notMem hyE]
  rw [inner_avgVec, integral_congr_ae (ae_restrict_of_ae h1), integral_const_mul, ← mul_assoc]
  congr 1
  rw [hr, ← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt measureReal_nonneg]

theorem norm_sum_inner_avgVec_sub_le (k : C(X × X, ℂ)) {ε : ℝ}
    (hk : ∀ i, ∀ x ∈ p.E i, ∀ y ∈ p.E i, ‖k (x, y) - k (x, x)‖ ≤ ε) :
    ‖∑ i : p.nonnull μ, ⟪p.avgVec μ i, contKernelOp μ k (p.avgVec μ i)⟫_ℂ -
      ∫ x, k (x, x) ∂μ‖ ≤ ε * μ.real univ := by
  have hkm : StronglyMeasurable (k : X × X → ℂ) :=
    (measurable_of_continuous_compactProd k.continuous).stronglyMeasurable
  have hdiag : Continuous fun x => k (x, x) := k.continuous.comp (continuous_id.prodMk continuous_id)
  have hrow : ∀ x, Continuous fun y => k (x, y) := fun x => k.continuous.comp
    (continuous_const.prodMk continuous_id)

  have hsplit : ∫ x, k (x, x) ∂μ = ∑ i : p.nonnull μ, ∫ x in p.E i, k (x, x) ∂μ := by
    rw [← setIntegral_univ, ← p.biUnion_eq, integral_biUnion_finset _
      (fun i _ => p.measurableSet i) (fun i _ j _ hij => p.disjoint hij)
      (fun i _ => (integrable_of_continuous_compact hdiag μ).integrableOn),
      Finset.sum_coe_sort (p.nonnull μ) (fun i => ∫ x in p.E i, k (x, x) ∂μ), nonnull,
      Finset.sum_filter_of_ne]
    intro i _ hne hzero
    exact hne (setIntegral_measure_zero _ hzero)
  rw [hsplit, ← Finset.sum_sub_distrib]

  have hpiece : ∀ i : p.nonnull μ, ‖(((μ.real (p.E i))⁻¹ : ℝ) : ℂ) *
      (∫ x in p.E i, ∫ y in p.E i, k (x, y) ∂μ ∂μ) - ∫ x in p.E i, k (x, x) ∂μ‖ ≤
      ε * μ.real (p.E i) := by
    intro i
    set E := p.E i
    set m := μ.real E
    have hm : 0 < m := measureReal_pos i
    have hEfin : μ E < ∞ := measure_lt_top μ E
    let F : X → ℂ := fun x => ∫ y in E, k (x, y) ∂μ
    have hFint : Integrable F (μ.restrict E) := by
      refine Integrable.of_bound (hkm.integral_prod_right' (ν := μ.restrict E)).aestronglyMeasurable
        (‖k‖ * m) (ae_of_all _ fun x => ?_)
      exact norm_setIntegral_le_of_norm_le_const hEfin fun y _ => k.norm_coe_le_norm _
    have hGint : Integrable (fun x => (m : ℂ) * k (x, x)) (μ.restrict E) :=
      (integrable_of_continuous_compact hdiag _).const_mul _
    have hdiagE : ∫ x in E, k (x, x) ∂μ =
        ((m⁻¹ : ℝ) : ℂ) * ∫ x in E, (m : ℂ) * k (x, x) ∂μ := by
      rw [integral_const_mul, ← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ hm.ne',
        Complex.ofReal_one, one_mul]
    rw [hdiagE, ← mul_sub, ← integral_sub hFint hGint, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (inv_pos.2 hm)]
    have hbound : ‖∫ x in E, (F x - (m : ℂ) * k (x, x)) ∂μ‖ ≤ (ε * m) * m := by
      refine norm_setIntegral_le_of_norm_le_const hEfin fun x hx => ?_
      have hrowE : Integrable (fun y => k (x, y)) (μ.restrict E) :=
        integrable_of_continuous_compact (hrow x) _
      have hconst : (m : ℂ) * k (x, x) = ∫ _ in E, k (x, x) ∂μ := by
        rw [setIntegral_const, Complex.real_smul]
      simp only [F]
      rw [hconst, ← integral_sub hrowE (integrable_const _)]
      exact norm_setIntegral_le_of_norm_le_const hEfin fun y hy => hk i x hx y hy
    calc m⁻¹ * ‖∫ x in E, (F x - (m : ℂ) * k (x, x)) ∂μ‖ ≤ m⁻¹ * ((ε * m) * m) := by
          gcongr
      _ = ε * m := by field_simp
  calc ‖∑ i : p.nonnull μ, (⟪p.avgVec μ i, contKernelOp μ k (p.avgVec μ i)⟫_ℂ -
        ∫ x in p.E i, k (x, x) ∂μ)‖
      ≤ ∑ i : p.nonnull μ, ‖⟪p.avgVec μ i, contKernelOp μ k (p.avgVec μ i)⟫_ℂ -
        ∫ x in p.E i, k (x, x) ∂μ‖ := norm_sum_le _ _
    _ ≤ ∑ i : p.nonnull μ, ε * μ.real (p.E i) := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [inner_avgVec_contKernelOp]
        exact hpiece i
    _ = ε * ∑ i ∈ p.nonnull μ, μ.real (p.E i) := by
        rw [← Finset.mul_sum, Finset.sum_coe_sort (p.nonnull μ) (fun i => μ.real (p.E i))]
    _ = ε * μ.real univ := by
        congr 1
        rw [nonnull, Finset.sum_filter_of_ne, ← measureReal_biUnion_finset
          (fun i _ j _ hij => p.disjoint hij) (fun i _ => p.measurableSet i), p.biUnion_eq]
        intro i _ hne hzero
        exact hne (by simp [Measure.real, hzero])

end MeasurablePartition

end Diagonal

section PositiveConj

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {ι : Type*} [Fintype ι]

end PositiveConj

section Approx

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [MeasurableSpace X]
  [BorelSpace X] (μ : Measure X) [IsFiniteMeasure μ]

namespace MeasurablePartition

variable (p : MeasurablePartition X)

omit [T2Space X] in

theorem norm_toLp_sub_avgProj_le {V : SetRel X X} (hp : p.IsFine V) (f : C(X, ℂ)) {ε : ℝ}
    (hε : 0 ≤ ε) (hf : ∀ x y, (x, y) ∈ V → ‖f x - f y‖ ≤ ε) :
    ‖ContinuousMap.toLp (E := ℂ) 2 μ ℂ f - p.avgProj μ (ContinuousMap.toLp (E := ℂ) 2 μ ℂ f)‖ ≤
      (measureUnivNNReal μ : ℝ) ^ (2 : ℝ≥0∞).toReal⁻¹ * ε := by
  classical
  set F := ContinuousMap.toLp (E := ℂ) 2 μ ℂ f
  have hne : ∀ i : p.nonnull μ, (p.E i).Nonempty := fun i =>
    nonempty_of_measure_ne_zero (Finset.mem_filter.1 i.2).2
  let pt : p.nonnull μ → X := fun i => (hne i).some
  let c : p.nonnull μ → ℂ := fun i => f (pt i) * ((Real.sqrt (μ.real (p.E i)) : ℝ) : ℂ)
  let g : Lp ℂ 2 μ := ∑ i, c i • p.avgVec μ i
  have hg : g ∈ Submodule.span ℂ (Set.range (p.avgVec μ)) :=
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  refine (norm_sub_finProj_le (p.orthonormal_avgVec μ) F hg).trans ?_
  refine Lp.norm_le_of_ae_bound hε ?_
  have hnull : ∀ᵐ x ∂μ, ∀ i, μ (p.E i) = 0 → x ∉ p.E i := by
    rw [ae_all_iff]
    intro i
    by_cases h : μ (p.E i) = 0
    · filter_upwards [measure_eq_zero_iff_ae_notMem.1 h] with x hx _ using hx
    · exact ae_of_all _ fun x h' => absurd h' h
  have hvec : ∀ᵐ x ∂μ, ∀ i : p.nonnull μ, (c i • p.avgVec μ i) x =
      c i * ((((Real.sqrt (μ.real (p.E i)))⁻¹ : ℝ) : ℂ) * (p.E i).indicator (fun _ => (1 : ℂ)) x) := by
    rw [ae_all_iff]
    intro i
    filter_upwards [Lp.coeFn_smul (c i) (p.avgVec μ i), coeFn_avgVec μ p i] with x h1 h2
    rw [h1, Pi.smul_apply, h2, smul_eq_mul]
  filter_upwards [Lp.coeFn_sub F g, ContinuousMap.coeFn_toLp (E := ℂ) (p := 2) (𝕜 := ℂ) μ f,
    Lp.coeFn_finsetSum Finset.univ (fun i => c i • p.avgVec μ i), hvec, hnull] with x h1 h2 h3 h4 h5
  rw [h1, Pi.sub_apply, h2, h3]
  simp_rw [h4]
  set j := p.index x
  have hxj : x ∈ p.E j := p.mem_index x
  have hjn : j ∈ p.nonnull μ :=
    Finset.mem_filter.2 ⟨Finset.mem_range.2 (p.index_lt x), fun h => h5 j h hxj⟩
  let j' : p.nonnull μ := ⟨j, hjn⟩
  rw [Finset.sum_eq_single j']
  · have hm : 0 < μ.real (p.E j) := measureReal_pos j'
    have hs : Real.sqrt (μ.real (p.E j)) ≠ 0 := (Real.sqrt_pos.2 hm).ne'
    have hval : c j' * ((((Real.sqrt (μ.real (p.E j)))⁻¹ : ℝ) : ℂ) *
        (p.E j).indicator (fun _ => (1 : ℂ)) x) = f (pt j') := by
      rw [Set.indicator_of_mem hxj, mul_one]
      simp only [c, j']
      rw [mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ hs, Complex.ofReal_one, mul_one]
    rw [hval]
    exact hf x (pt j') (hp j x hxj (pt j') (hne j').some_mem)
  · intro i _ hij
    have hx : x ∉ p.E i := fun hx => hij (Subtype.ext ((p.index_eq_iff).2 hx).symm)
    rw [Set.indicator_of_notMem hx, mul_zero, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ j') h

end MeasurablePartition

end Approx

section Uniform

variable {X : Type*} [UniformSpace X] [CompactSpace X] [T2Space X] [MeasurableSpace X]
  [BorelSpace X] (μ : Measure X) [IsFiniteMeasure μ]

open MeasurablePartition

theorem tendsto_finePart_avgProj [μ.WeaklyRegular] (y : Lp ℂ 2 μ) :
    Tendsto (fun V => (finePart V).avgProj μ y) (fineFilter X) (𝓝 y) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨f, hf⟩ := (ContinuousMap.toLp_denseRange (E := ℂ) (μ := μ) (𝕜 := ℂ) (p := 2)
    ENNReal.ofNat_ne_top).exists_dist_lt y (half_pos hε)
  set C : ℝ := (measureUnivNNReal μ : ℝ) ^ (2 : ℝ≥0∞).toReal⁻¹
  have hC : 0 ≤ C := by positivity
  set δ : ℝ := ε / (2 * (C + 1))
  have hδ : 0 < δ := by positivity
  have hW := CompactSpace.uniformContinuous_of_continuous f.continuous (Metric.dist_mem_uniformity hδ)
  filter_upwards [eventually_finePart_isFine hW] with V hV
  set F := ContinuousMap.toLp (E := ℂ) 2 μ ℂ f
  set P := (finePart V).avgProj μ
  have h1 : ‖F - P F‖ ≤ C * δ := by
    refine norm_toLp_sub_avgProj_le μ _ hV f hδ.le fun x y hxy => ?_
    rw [← dist_eq_norm]
    exact (show dist (f x) (f y) < δ from hxy).le
  have h2 : ‖y - P y‖ ≤ ‖y - P F‖ :=
    norm_sub_finProj_le ((finePart V).orthonormal_avgVec μ) y (finProj_mem_span _ F)
  have h3 : C * δ < ε / 2 := by
    have : C * δ = ε / 2 * (C / (C + 1)) := by simp only [δ]; field_simp
    rw [this]
    have : C / (C + 1) < 1 := (div_lt_one (by positivity)).2 (lt_add_one C)
    nlinarith
  rw [dist_eq_norm, norm_sub_rev]
  calc ‖y - P y‖ ≤ ‖y - P F‖ := h2
    _ = ‖(y - F) + (F - P F)‖ := by rw [sub_add_sub_cancel]
    _ ≤ ‖y - F‖ + ‖F - P F‖ := norm_add_le _ _
    _ < ε / 2 + ε / 2 := by
        rw [← dist_eq_norm]
        exact add_lt_add_of_lt_of_le hf (h1.trans h3.le)
    _ = ε := add_halves ε

theorem tendsto_sum_inner_avgVec (k : C(X × X, ℂ)) :
    Tendsto (fun V => ∑ i : (finePart V).nonnull μ,
      ⟪(finePart V).avgVec μ i, contKernelOp μ k ((finePart V).avgVec μ i)⟫_ℂ) (fineFilter X)
      (𝓝 (∫ x, k (x, x) ∂μ)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  set δ : ℝ := ε / (μ.real univ + 1)
  have hδ : 0 < δ := by positivity
  have hW := CompactSpace.uniformContinuous_of_continuous k.continuous
    (Metric.dist_mem_uniformity hδ)
  obtain ⟨u, hu, v, hv, huv⟩ := entourageProd_subset hW
  filter_upwards [eventually_finePart_isFine (inter_mem hu hv)] with V hV
  rw [dist_eq_norm]
  refine lt_of_le_of_lt (norm_sum_inner_avgVec_sub_le μ _ k (ε := δ) fun i x hx y hy => ?_) ?_
  · have hmem : ((x, y), (x, x)) ∈ entourageProd u v :=
      ⟨refl_mem_uniformity hu, (hV i y hy x hx).2⟩
    have := huv hmem
    rw [← dist_eq_norm]
    exact (show dist (k (x, y)) (k (x, x)) < δ from this).le
  · have h : δ * μ.real univ = ε * (μ.real univ / (μ.real univ + 1)) := by
      simp only [δ]; field_simp
    rw [h]
    have : μ.real univ / (μ.real univ + 1) < 1 :=
      (div_lt_one (by positivity)).2 (lt_add_one _)
    nlinarith [measureReal_nonneg (μ := μ) (s := univ)]

theorem trace_contKernelOp_of_uniformSpace [μ.WeaklyRegular] (k : C(X × X, ℂ))
    (hT : IsTraceClass (contKernelOp μ k)) : trace (contKernelOp μ k) = ∫ x, k (x, x) ∂μ := by
  have h1 := tendsto_trace_comp hT (fun V => (finePart V).avgProj μ)
    (fun V x => norm_sub_finProj_le_norm ((finePart V).orthonormal_avgVec μ) x)
    (tendsto_finePart_avgProj μ)
  have h2 := tendsto_sum_inner_avgVec μ k
  refine tendsto_nhds_unique h1 (h2.congr fun V => ?_)
  exact (trace_comp_finProj _ _).symm

end Uniform

section Main

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [MeasurableSpace X]
  [BorelSpace X] (μ : Measure X) [IsFiniteMeasure μ] [μ.WeaklyRegular]

theorem trace_contKernelOp (k : C(X × X, ℂ)) (hT : IsTraceClass (contKernelOp μ k)) :
    trace (contKernelOp μ k) = ∫ x, k (x, x) ∂μ := by
  let _ : UniformSpace X := uniformSpaceOfCompactR1
  exact trace_contKernelOp_of_uniformSpace μ k hT

end Main

end

end GroundTheory.Automorphic
