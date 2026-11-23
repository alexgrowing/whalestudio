import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.SimpleSum
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormalizedAbsCharacterization
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LinearChangeOfVariablesLocalFieldMatrix

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open scoped ENNReal NNReal

namespace GlobalTheory.SplitWeil

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k] {n : Type} [Fintype n] [DecidableEq n]
  (ν : Measure k) [ν.IsAddHaarMeasure]

theorem map_mul_left_volM (h : GL n k) :
    (volM ν n n).map (fun x => h.val * x) =
      ENNReal.ofReal (nabs k (Matrix.GeneralLinearGroup.det h) ^ (-(Fintype.card n : ℝ))) • volM ν n n := by
  haveI := secondCountable k
  haveI := t2Space k
  haveI : BorelSpace (Matrix n n k) := inferInstanceAs (BorelSpace (n → n → k))
  haveI : LocallyCompactSpace (Matrix n n k) := inferInstanceAs (LocallyCompactSpace (n → n → k))
  haveI : SecondCountableTopology (Matrix n n k) := inferInstanceAs (SecondCountableTopology (n → n → k))
  haveI : (volM ν n n).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  let e : Matrix n n k ≃+ Matrix n n k :=
    { toFun := fun x => h.val * x
      invFun := fun x => (h⁻¹).val * x
      left_inv := fun x => by simp only [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
      right_inv := fun x => by simp only [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
      map_add' := fun x y => Matrix.mul_add _ _ _ }
  have c1 : Continuous e := continuous_const.matrix_mul continuous_id
  have c2 : Continuous e.symm := continuous_const.matrix_mul continuous_id
  haveI := e.isAddHaarMeasure_map (volM ν n n) c1 c2
  obtain ⟨c, hc⟩ : ∃ c : ℝ≥0, (volM ν n n).map e = c • volM ν n n :=
    ⟨_, Measure.isAddLeftInvariant_eq_smul _ _⟩
  change (volM ν n n).map e = _
  set K : Set (Matrix n n k) := {A | ∀ i j, A i j ∈ 𝒪[k]} with hK
  have hKo : IsOpen K := SplitFlip.isOpen_intMatrix
  have hKc : IsCompact K := SplitFlip.isCompact_intMatrix
  have h0 : volM ν n n K ≠ 0 := (hKo.measure_pos _ ⟨0, fun _ _ => zero_mem _⟩).ne'
  have ht : volM ν n n K ≠ ⊤ := hKc.measure_lt_top.ne
  have hr : (volM ν n n).real K ≠ 0 := by simp [Measure.real, ENNReal.toReal_eq_zero_iff, h0, ht]
  have key := integral_comp_mul_mul_volM ν (1 : GL n k) h (K.indicator fun _ => (1 : ℂ))
  have h1 : ∫ x, K.indicator (fun _ => (1 : ℂ)) (h.val * x * (1 : GL n k).val) ∂(volM ν n n) =
      ∫ x, K.indicator (fun _ => (1 : ℂ)) x ∂((volM ν n n).map e) := by
    rw [integral_map c1.measurable.aemeasurable
      (stronglyMeasurable_const.indicator hKo.measurableSet).aestronglyMeasurable]
    simp only [Units.val_one, Matrix.mul_one]
    rfl
  rw [h1, hc, integral_smul_nnreal_measure, integral_indicator_const _ hKo.measurableSet, map_one, nabs_one,
    Real.one_rpow, mul_one] at key
  have h2 : (c : ℝ) = nabs k (Matrix.GeneralLinearGroup.det h) ^ (-(Fintype.card n : ℝ)) := by
    refine mul_right_cancel₀ hr ?_
    simp only [NNReal.smul_def, smul_smul, Complex.real_smul, mul_one] at key
    exact_mod_cast key
  rw [hc, ← h2, ENNReal.ofReal_coe_nnreal]
  rfl

omit [MeasurableSpace k] [BorelSpace k] in
theorem continuous_density_volGL : Continuous fun g : GL n k =>
    ENNReal.ofReal (nabs k (Matrix.GeneralLinearGroup.det g) ^ (-(Fintype.card n : ℝ))) :=
  (((isLocallyConstant_nabs k).comp_continuous Matrix.GeneralLinearGroup.continuous_det).comp
    (fun t : ℝ => ENNReal.ofReal (t ^ (-(Fintype.card n : ℝ))))).continuous

theorem isMulLeftInvariant_volGL : (volGL ν n).IsMulLeftInvariant := by
  haveI := secondCountable k
  haveI : BorelSpace (Matrix n n k) := inferInstanceAs (BorelSpace (n → n → k))
  have hE := Model.measurableEmbedding_val (k := k) n
  have hd := (continuous_density_volGL (k := k) (n := n)).measurable
  set μ := (volM ν n n).comap (fun g : GL n k => g.val) with hμ
  set d := fun g : GL n k =>
    ENNReal.ofReal (nabs k (Matrix.GeneralLinearGroup.det g) ^ (-(Fintype.card n : ℝ))) with hdd
  have dmul : ∀ g h, d (g * h) = d g * d h := fun g h => by
    simp only [hdd, map_mul, nabs_mul]
    rw [Real.mul_rpow (nabs_pos' _).le (nabs_pos' _).le,
      ENNReal.ofReal_mul (Real.rpow_nonneg (nabs_pos' _).le _)]
  have done' : d 1 = 1 := by simp [hdd, nabs_one]
  have hm : ∀ h : GL n k, μ.map (fun x => h * x) = d h • μ := fun h => by
    ext s hs
    have cm : Measurable fun x : Matrix n n k => h.val * x :=
      (continuous_const.matrix_mul continuous_id).measurable
    rw [Measure.map_apply (measurable_const_mul h) hs, Measure.smul_apply, hE.comap_apply, hE.comap_apply,
      ← Measure.smul_apply, ← map_mul_left_volM ν h, Measure.map_apply cm (hE.measurableSet_image.2 hs)]
    congr 1
    ext x
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact ⟨h * g, hg, rfl⟩
    · rintro ⟨g, hg, e⟩
      refine ⟨h⁻¹ * g, by simpa using hg, ?_⟩
      have e' : g.val = h.val * x := e
      simp only [Units.val_mul, e', ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
  refine ⟨fun h => ?_⟩
  ext s hs
  have hs' := measurable_const_mul h hs
  change (μ.withDensity d).map _ s = μ.withDensity d s
  rw [Measure.map_apply (measurable_const_mul h) hs, withDensity_apply _ hs', withDensity_apply _ hs,
    ← lintegral_indicator hs', ← lintegral_indicator hs]
  have e1 : ∀ x, ((fun x => h * x) ⁻¹' s).indicator d x = d h⁻¹ * s.indicator d (h * x) := fun x => by
    by_cases hx : h * x ∈ s
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (show x ∈ (fun x => h * x) ⁻¹' s from hx), ← dmul,
        inv_mul_cancel_left]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (show x ∉ (fun x => h * x) ⁻¹' s from hx),
        mul_zero]
  simp_rw [e1]
  rw [lintegral_const_mul _ (f := fun a => s.indicator d (h * a))
      ((hd.indicator hs).comp (measurable_const_mul h)),
    ← lintegral_map (hd.indicator hs) (measurable_const_mul h), hm, lintegral_smul_measure, smul_eq_mul,
    ← mul_assoc, ← dmul, inv_mul_cancel, done', one_mul]

theorem volGL_KO : volGL ν n (KO k n) = volM ν n n ((fun g : GL n k => g.val) '' (KO k n)) := by
  have hE := Model.measurableEmbedding_val (k := k) n
  have hs := (SplitFlip.isOpen_KO (k := k) (n := n)).measurableSet
  unfold volGL
  rw [withDensity_apply _ hs, setLIntegral_congr_fun hs (g := fun _ => 1), setLIntegral_one, hE.comap_apply]
  rintro _ ⟨u, rfl⟩
  have h1 : nabs k (Matrix.GeneralLinearGroup.det
      (Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) u)) = 1 := by
    rw [nabs_eq_one_iff]
    have : ((Matrix.GeneralLinearGroup.det
      (Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) u) : kˣ) : k) = algebraMap 𝒪[k] k u.val.det :=
      ((algebraMap 𝒪[k] k).map_det u.val).symm
    rw [this]
    exact (Valuation.integer.integers (valuation k)).one_of_isUnit
      ((Matrix.isUnit_iff_isUnit_det _).1 u.isUnit)
  simp only [h1, Real.one_rpow, ENNReal.ofReal_one]

theorem isHaarMeasure_volGL : (volGL ν n).IsHaarMeasure := by
  haveI := secondCountable k
  haveI := t2Space k
  haveI : (volM ν n n).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  haveI := isMulLeftInvariant_volGL (n := n) ν
  have ho := SplitFlip.isOpen_KO (k := k) (n := n)
  have hc := SplitFlip.isCompact_KO (k := k) (n := n)
  have hoe : Topology.IsOpenEmbedding (fun g : GL n k => g.val) := by
    refine ⟨SplitFlip.isEmbedding_val_GL, ?_⟩
    have : Set.range (fun g : GL n k => g.val) = {x : Matrix n n k | x.det ≠ 0} := by
      ext x
      simp only [Set.mem_range, Set.mem_setOf_eq]
      rw [← isUnit_iff_ne_zero, ← Matrix.isUnit_iff_isUnit_det]
      rfl
    rw [this]
    exact isOpen_ne_fun (continuous_id.matrix_det) continuous_const
  refine Measure.isHaarMeasure_of_isCompact_nonempty_interior _ _ hc
    (by rw [ho.interior_eq]; exact ⟨1, one_mem _⟩) ?_ ?_
  · rw [volGL_KO]
    exact ((hoe.isOpenMap _ ho).measure_pos _ ⟨_, 1, one_mem _, rfl⟩).ne'
  · rw [volGL_KO]
    exact (hc.image hoe.continuous).measure_lt_top.ne

theorem volGL_haar : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (ν : Measure k) [ν.IsAddHaarMeasure], BorelSpace (GL n k) ∧ LocallyCompactSpace (GL n k) ∧ SecondCountableTopology (GL n k) ∧ IsCompact (KO k n : Set (GL n k)) ∧ IsOpen (KO k n : Set (GL n k)) ∧ IsOpen (KOne k n : Set (GL n k)) ∧ (volGL ν n).IsHaarMeasure ∧ (volGL ν n).IsMulRightInvariant :=
  fun _ _ _ _ _ _ _ n _ _ ν _ =>
    haveI := isHaarMeasure_volGL (n := n) ν
    ⟨SplitFlip.borel_GL, SplitFlip.locallyCompact_GL, SplitFlip.secondCountable_GL, SplitFlip.isCompact_KO,
      SplitFlip.isOpen_KO, StepData.isOpen_KOne, this, SplitFlip.isMulRightInvariant_of_haar _⟩

end GlobalTheory.SplitWeil
