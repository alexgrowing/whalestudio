import Mathlib
import GroundTheory.GlobalFields.TateThesis.IdeleMeasure

open NumberField IsDedekindDomain Topology Filter MeasureTheory TopologicalSpace Real
open scoped NumberField.AdeleRing ENNReal NNReal

namespace GroundTheory.Global

noncomputable section

section PosReal

instance isTopologicalGroup_posReal : IsTopologicalGroup {r : ℝ // 0 < r} where
  continuous_mul := ((continuous_subtype_val.comp continuous_fst).mul
    (continuous_subtype_val.comp continuous_snd)).subtype_mk _
  continuous_inv := (continuous_subtype_val.inv₀ fun r ↦ r.2.ne').subtype_mk _

instance locallyCompactSpace_posReal : LocallyCompactSpace {r : ℝ // 0 < r} :=
  (isOpen_Ioi (a := (0 : ℝ))).isOpenEmbedding_subtypeVal.locallyCompactSpace

def expPos (x : ℝ) : {r : ℝ // 0 < r} := ⟨exp x, exp_pos x⟩

@[simp] theorem coe_expPos (x : ℝ) : (expPos x : ℝ) = exp x := rfl

def expPosHomeomorph : ℝ ≃ₜ {r : ℝ // 0 < r} where
  toFun := expPos
  invFun r := log r
  left_inv x := log_exp x
  right_inv r := Subtype.ext (exp_log r.2)
  continuous_toFun := continuous_exp.subtype_mk _
  continuous_invFun := continuous_subtype_val.log fun r ↦ r.2.ne'

theorem expPos_add (x y : ℝ) : expPos (x + y) = expPos x * expPos y :=
  Subtype.ext (exp_add x y)

theorem measurable_expPos : Measurable expPos := expPosHomeomorph.continuous.measurable

def posRealMeasure : Measure {r : ℝ // 0 < r} :=
  Measure.comap Subtype.val (volume.withDensity fun t : ℝ ↦ ENNReal.ofReal t⁻¹)

theorem measurableEmbedding_posReal_val :
    MeasurableEmbedding (Subtype.val : {r : ℝ // 0 < r} → ℝ) :=
  MeasurableEmbedding.subtype_coe measurableSet_Ioi

theorem posRealMeasure_eq_map_expPos : posRealMeasure = Measure.map expPos volume := by
  ext S hS
  rw [posRealMeasure, measurableEmbedding_posReal_val.comap_apply,
    withDensity_apply _ (measurableEmbedding_posReal_val.measurableSet_image' hS),
    Measure.map_apply measurable_expPos hS]
  set s : Set ℝ := expPos ⁻¹' S
  have hs : MeasurableSet s := measurable_expPos hS
  have himg : exp '' s = Subtype.val '' S := by
    ext t
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨expPos x, hx, rfl⟩
    · rintro ⟨r, hr, rfl⟩
      refine ⟨log r, ?_, exp_log r.2⟩
      change expPos (log r) ∈ S
      convert hr
      exact Subtype.ext (exp_log r.2)
  rw [← himg, lintegral_image_eq_lintegral_abs_deriv_mul hs
    (fun x _ ↦ (hasDerivAt_exp x).hasDerivWithinAt) (exp_injective.injOn)]
  rw [← setLIntegral_one]
  refine setLIntegral_congr_fun hs fun x _ ↦ ?_
  rw [abs_of_pos (exp_pos x), ← ENNReal.ofReal_mul (exp_pos x).le, mul_inv_cancel₀ (exp_pos x).ne',
    ENNReal.ofReal_one]

instance isHaarMeasure_posRealMeasure : posRealMeasure.IsHaarMeasure := by
  rw [posRealMeasure_eq_map_expPos]
  have h1 : (Measure.map expPos volume).IsMulLeftInvariant := by
    refine ⟨fun a ↦ ?_⟩
    rw [Measure.map_map (measurable_const_mul a) measurable_expPos]
    have : (fun x ↦ a * x) ∘ expPos = expPos ∘ (fun x ↦ log a + x) := by
      funext x
      simp only [Function.comp_apply, expPos_add]
      congr 1
      exact Subtype.ext (exp_log a.2).symm
    rw [this, ← Measure.map_map measurable_expPos (measurable_const_add _),
      map_add_left_eq_self]
  have h2 : IsFiniteMeasureOnCompacts (Measure.map expPos volume) := by
    refine ⟨fun C hC ↦ ?_⟩
    rw [Measure.map_apply measurable_expPos hC.isClosed.measurableSet]
    exact (expPosHomeomorph.isCompact_preimage.2 hC).measure_lt_top
  have h3 : (Measure.map expPos volume).IsOpenPosMeasure := by
    refine ⟨fun U hU hne ↦ ?_⟩
    rw [Measure.map_apply measurable_expPos hU.measurableSet]
    exact (hU.preimage expPosHomeomorph.continuous).measure_ne_zero volume
      (hne.preimage expPosHomeomorph.surjective)
  exact {}

theorem integral_posRealMeasure {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) :
    ∫ t, f t ∂posRealMeasure = ∫ t in Set.Ioi (0 : ℝ), t⁻¹ • f t := by
  rw [posRealMeasure_eq_map_expPos]
  change ∫ t, f t ∂Measure.map expPosHomeomorph.toMeasurableEquiv volume = _
  rw [integral_map_equiv expPosHomeomorph.toMeasurableEquiv (fun t ↦ f t), ← Real.range_exp,
    ← Set.image_univ, integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ
      (fun x _ ↦ (hasDerivAt_exp x).hasDerivWithinAt) exp_injective.injOn, Measure.restrict_univ]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
  simp only [abs_of_pos (exp_pos x), smul_smul, mul_inv_cancel₀ (exp_pos x).ne', one_smul]
  rfl

end PosReal

section ModuleSection

open InfinitePlace InfinitePlace.Completion IdeleGroup

variable {K : Type*} [Field K]

def posRealElem (w : InfinitePlace K) (t : ℝ) : w.Completion :=
  open Classical in
  if hw : w.IsReal then (ringEquivRealOfIsReal hw).symm t
  else (ringEquivComplexOfIsComplex (not_isReal_iff_isComplex.1 hw)).symm (Real.sqrt t : ℂ)

theorem posRealElem_mul (w : InfinitePlace K) {s t : ℝ} (hs : 0 ≤ s) :
    posRealElem w (s * t) = posRealElem w s * posRealElem w t := by
  unfold posRealElem
  split_ifs with hw
  · exact map_mul _ s t
  · rw [Real.sqrt_mul hs, Complex.ofReal_mul, map_mul]

theorem posRealElem_one (w : InfinitePlace K) : posRealElem w 1 = 1 := by
  unfold posRealElem
  split_ifs with hw
  · exact map_one _
  · rw [Real.sqrt_one, Complex.ofReal_one, map_one]

theorem norm_posRealElem_pow (w : InfinitePlace K) {t : ℝ} (ht : 0 ≤ t) :
    ‖posRealElem w t‖ ^ w.mult = t := by
  unfold posRealElem
  split_ifs with hw
  · have h : ‖(ringEquivRealOfIsReal hw).symm t‖ = ‖t‖ :=
      (isometryEquivRealOfIsReal hw).symm.isometry.norm_map_of_map_zero
        (map_zero (ringEquivRealOfIsReal hw).symm) t
    rw [h, mult, if_pos hw, pow_one, Real.norm_of_nonneg ht]
  · have hc := not_isReal_iff_isComplex.1 hw
    have h : ‖(ringEquivComplexOfIsComplex hc).symm (Real.sqrt t : ℂ)‖ = ‖(Real.sqrt t : ℂ)‖ :=
      (isometryEquivComplexOfIsComplex hc).symm.isometry.norm_map_of_map_zero
        (map_zero (ringEquivComplexOfIsComplex hc).symm) _
    rw [h, mult, if_neg hw, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg t),
      Real.sq_sqrt ht]

theorem posRealElem_ne_zero (w : InfinitePlace K) {t : ℝ} (ht : 0 < t) : posRealElem w t ≠ 0 := by
  intro h
  have := norm_posRealElem_pow w ht.le
  rw [h, norm_zero, zero_pow (by unfold mult; split_ifs <;> norm_num)] at this
  exact ht.ne this

theorem continuous_posRealElem (w : InfinitePlace K) : Continuous (posRealElem w) := by
  unfold posRealElem
  split_ifs with hw
  · exact (isometryEquivRealOfIsReal hw).symm.continuous
  · exact (isometryEquivComplexOfIsComplex (not_isReal_iff_isComplex.1 hw)).symm.continuous.comp
      (Complex.continuous_ofReal.comp Real.continuous_sqrt)

def posRealToUnits (w : InfinitePlace K) : {r : ℝ // 0 < r} →* (w.Completion)ˣ where
  toFun t := Units.mk0 (posRealElem w t) (posRealElem_ne_zero w t.2)
  map_one' := Units.ext (posRealElem_one w)
  map_mul' s _ := Units.ext (posRealElem_mul w s.2.le)

theorem continuous_posRealToUnits (w : InfinitePlace K) : Continuous (posRealToUnits w) :=
  Units.continuous_iff.2 ⟨(continuous_posRealElem w).comp continuous_subtype_val,
    ((continuous_posRealElem w).comp continuous_subtype_val).inv₀ fun t ↦
      posRealElem_ne_zero w t.2⟩

variable [NumberField K]

def moduleSection (w : InfinitePlace K) : {r : ℝ // 0 < r} →* IdeleGroup K :=
  (infiniteEmbedding w).comp (posRealToUnits w)

theorem continuous_moduleSection (w : InfinitePlace K) : Continuous (moduleSection w) :=
  (continuous_infiniteEmbedding w).comp (continuous_posRealToUnits w)

@[simp]
theorem ideleModule_moduleSection (w : InfinitePlace K) (t : {r : ℝ // 0 < r}) :
    ideleModule K (moduleSection w t) = t := by
  refine Subtype.ext ?_
  rw [moduleSection, MonoidHom.comp_apply, ideleModule_infiniteEmbedding]
  exact norm_posRealElem_pow w t.2.le

end ModuleSection

section Splitting

open IdeleGroup

variable {K : Type*} [Field K] [NumberField K]

instance secondCountableTopology_normOneSubgroup :
    SecondCountableTopology (normOneSubgroup K) :=
  IsEmbedding.subtypeVal.secondCountableTopology

instance locallyCompactSpace_normOneSubgroup : LocallyCompactSpace (normOneSubgroup K) :=
  (isClosed_normOneSubgroup K).isClosedEmbedding_subtypeVal.locallyCompactSpace

theorem mul_inv_moduleSection_mem (w : InfinitePlace K) (x : IdeleGroup K) :
    x * (moduleSection w (ideleModule K x))⁻¹ ∈ normOneSubgroup K := by
  rw [normOneSubgroup, MonoidHom.mem_ker, map_mul, map_inv, ideleModule_moduleSection,
    mul_inv_cancel]

def normOneSplitting (w : InfinitePlace K) :
    IdeleGroup K ≃ₜ* normOneSubgroup K × {r : ℝ // 0 < r} where
  toFun x := (⟨x * (moduleSection w (ideleModule K x))⁻¹, mul_inv_moduleSection_mem w x⟩,
    ideleModule K x)
  invFun p := (p.1 : IdeleGroup K) * moduleSection w p.2
  left_inv x := by simp
  right_inv p := by
    obtain ⟨⟨u, hu⟩, t⟩ := p
    have hu' : ideleModule K u = 1 := hu
    refine Prod.ext (Subtype.ext ?_) ?_
    · simp [hu']
    · simp [hu']
  map_mul' x y := by
    refine Prod.ext (Subtype.ext ?_) (map_mul _ x y)
    change x * y * (moduleSection w (ideleModule K (x * y)))⁻¹ =
      x * (moduleSection w (ideleModule K x))⁻¹ * (y * (moduleSection w (ideleModule K y))⁻¹)
    simp only [map_mul, mul_inv]
    ac_rfl
  continuous_toFun := by
    refine Continuous.prodMk ?_ (continuous_ideleModule)
    exact (continuous_id.mul ((continuous_moduleSection w).comp continuous_ideleModule).inv)
      |>.subtype_mk _
  continuous_invFun :=
    (continuous_subtype_val.comp continuous_fst).mul
      ((continuous_moduleSection w).comp continuous_snd)

@[simp]
theorem normOneSplitting_apply_snd (w : InfinitePlace K) (x : IdeleGroup K) :
    (normOneSplitting w x).2 = ideleModule K x :=
  rfl

@[simp]
theorem normOneSplitting_symm_apply (w : InfinitePlace K)
    (p : normOneSubgroup K × {r : ℝ // 0 < r}) :
    (normOneSplitting w).symm p = (p.1 : IdeleGroup K) * moduleSection w p.2 :=
  rfl

end Splitting

section ProdHaar

variable {G H : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
  [BorelSpace G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [MeasurableSpace H]
  [BorelSpace H] [LocallyCompactSpace H] [SecondCountableTopology H]

theorem map_fst_restrict_eq_smul_haar (lam : Measure (G × H)) [lam.IsHaarMeasure]
    (ν : Measure H) [ν.IsHaarMeasure] {S : Set H} (hν : ν S = 1) :
    Measure.map Prod.fst (lam.restrict (Set.univ ×ˢ S)) =
      lam.haarScalarFactor ((Measure.haar : Measure G).prod ν) • (Measure.haar : Measure G) := by
  conv_lhs => rw [Measure.isMulLeftInvariant_eq_smul lam ((Measure.haar : Measure G).prod ν)]
  rw [Measure.restrict_smul, Measure.map_smul, ← Measure.prod_restrict, Measure.restrict_univ,
    Measure.map_fst_prod, Measure.restrict_apply_univ, hν, one_smul]

theorem isHaarMeasure_map_fst_restrict (lam : Measure (G × H)) [lam.IsHaarMeasure]
    (ν : Measure H) [ν.IsHaarMeasure] {S : Set H} (hν : ν S = 1) :
    (Measure.map Prod.fst (lam.restrict (Set.univ ×ˢ S))).IsHaarMeasure := by
  rw [map_fst_restrict_eq_smul_haar lam ν hν]
  exact Measure.IsHaarMeasure.nnreal_smul _
    (Measure.haarScalarFactor_pos_of_isHaarMeasure _ _).ne'

theorem eq_prod_map_fst_restrict (lam : Measure (G × H)) [lam.IsHaarMeasure]
    (ν : Measure H) [ν.IsHaarMeasure] {S : Set H} (hν : ν S = 1) :
    lam = (Measure.map Prod.fst (lam.restrict (Set.univ ×ˢ S))).prod ν := by
  rw [map_fst_restrict_eq_smul_haar lam ν hν, Measure.prod_smul_left]
  exact Measure.isMulLeftInvariant_eq_smul lam _

end ProdHaar

section NormOneMeasure

open IdeleGroup

variable (K : Type*) [Field K] [NumberField K]

def posRealUnitInterval : Set {r : ℝ // 0 < r} := Subtype.val ⁻¹' Set.Icc 1 (exp 1)

theorem measurableSet_posRealUnitInterval : MeasurableSet posRealUnitInterval :=
  measurable_subtype_coe measurableSet_Icc

theorem posRealMeasure_posRealUnitInterval : posRealMeasure posRealUnitInterval = 1 := by
  rw [posRealMeasure_eq_map_expPos, Measure.map_apply measurable_expPos
    measurableSet_posRealUnitInterval]
  have : expPos ⁻¹' posRealUnitInterval = Set.Icc 0 1 := by
    ext x
    simp only [posRealUnitInterval, Set.mem_preimage, Set.mem_Icc, coe_expPos]
    rw [one_le_exp_iff, exp_le_exp]
  rw [this, Real.volume_Icc, sub_zero, ENNReal.ofReal_one]

variable {K}

def normOneMeasureAt (w : InfinitePlace K) : Measure (normOneSubgroup K) :=
  Measure.map Prod.fst
    (((ideleMeasure K).map (normOneSplitting w)).restrict (Set.univ ×ˢ posRealUnitInterval))

instance isHaarMeasure_map_normOneSplitting (w : InfinitePlace K) :
    ((ideleMeasure K).map (normOneSplitting w)).IsHaarMeasure :=
  ContinuousMulEquiv.isHaarMeasure_map _ _

instance isHaarMeasure_normOneMeasureAt (w : InfinitePlace K) :
    (normOneMeasureAt w).IsHaarMeasure :=
  isHaarMeasure_map_fst_restrict _ posRealMeasure posRealMeasure_posRealUnitInterval

theorem map_normOneSplitting_eq_prod_at (w : InfinitePlace K) :
    (ideleMeasure K).map (normOneSplitting w) = (normOneMeasureAt w).prod posRealMeasure :=
  eq_prod_map_fst_restrict _ posRealMeasure posRealMeasure_posRealUnitInterval

end NormOneMeasure

section Independence

open IdeleGroup

variable {K : Type*} [Field K] [NumberField K]

theorem moduleSection_mul_inv_mem (w w' : InfinitePlace K) (t : {r : ℝ // 0 < r}) :
    moduleSection w t * (moduleSection w' t)⁻¹ ∈ normOneSubgroup K := by
  rw [normOneSubgroup, MonoidHom.mem_ker, map_mul, map_inv, ideleModule_moduleSection,
    ideleModule_moduleSection, mul_inv_cancel]

theorem normOneMeasureAt_eq (w w' : InfinitePlace K) :
    normOneMeasureAt w' = normOneMeasureAt w := by
  set m := normOneMeasureAt w
  let c : {r : ℝ // 0 < r} → normOneSubgroup K := fun t ↦
    ⟨moduleSection w t * (moduleSection w' t)⁻¹, moduleSection_mul_inv_mem w w' t⟩
  have hc : Continuous c :=
    ((continuous_moduleSection w).mul (continuous_moduleSection w').inv).subtype_mk _
  let φ : normOneSubgroup K × {r : ℝ // 0 < r} → normOneSubgroup K × {r : ℝ // 0 < r} :=
    fun p ↦ (c p.2 * p.1, p.2)
  have hsplit : (normOneSplitting w' : IdeleGroup K → _) = φ ∘ normOneSplitting w := by
    funext x
    refine Prod.ext (Subtype.ext ?_) rfl
    change x * (moduleSection w' (ideleModule K x))⁻¹ =
      moduleSection w (ideleModule K x) * (moduleSection w' (ideleModule K x))⁻¹ *
        (x * (moduleSection w (ideleModule K x))⁻¹)
    generalize moduleSection w (ideleModule K x) = a
    generalize moduleSection w' (ideleModule K x) = b
    rw [show a * b⁻¹ * (x * a⁻¹) = (a * a⁻¹) * (x * b⁻¹) by ac_rfl, mul_inv_cancel, one_mul]
  have hψ : MeasurePreserving (fun p : {r : ℝ // 0 < r} × normOneSubgroup K ↦ (id p.1, c p.1 * p.2))
      (posRealMeasure.prod m) (posRealMeasure.prod m) :=
    (MeasurePreserving.id posRealMeasure).skew_product (g := fun t u ↦ c t * u)
      ((hc.comp continuous_fst).mul continuous_snd).measurable
      (Filter.Eventually.of_forall fun t ↦ map_mul_left_eq_self m (c t))
  have hφ : MeasurePreserving φ (m.prod posRealMeasure) (m.prod posRealMeasure) :=
    Measure.measurePreserving_swap.comp (hψ.comp Measure.measurePreserving_swap)
  have hmap : (ideleMeasure K).map (normOneSplitting w') = m.prod posRealMeasure := by
    rw [hsplit, ← Measure.map_map hφ.measurable (map_continuous _).measurable,
      map_normOneSplitting_eq_prod_at w, hφ.map_eq]
  rw [normOneMeasureAt, hmap, ← Measure.prod_restrict, Measure.restrict_univ,
    Measure.map_fst_prod, Measure.restrict_apply_univ, posRealMeasure_posRealUnitInterval, one_smul]

end Independence

section Canonical

open IdeleGroup

variable (K : Type*) [Field K] [NumberField K]

def normOneMeasure : Measure (normOneSubgroup K) :=
  normOneMeasureAt (Classical.arbitrary (InfinitePlace K))

instance isHaarMeasure_normOneMeasure : (normOneMeasure K).IsHaarMeasure := by
  unfold normOneMeasure
  infer_instance

variable {K}

theorem normOneMeasureAt_eq_normOneMeasure (w : InfinitePlace K) :
    normOneMeasureAt w = normOneMeasure K :=
  normOneMeasureAt_eq _ w

theorem map_normOneSplitting_eq_prod (w : InfinitePlace K) :
    (ideleMeasure K).map (normOneSplitting w) = (normOneMeasure K).prod posRealMeasure := by
  rw [← normOneMeasureAt_eq_normOneMeasure w, map_normOneSplitting_eq_prod_at]

theorem measurePreserving_normOneSplitting (w : InfinitePlace K) :
    MeasurePreserving (normOneSplitting w) (ideleMeasure K)
      ((normOneMeasure K).prod posRealMeasure) :=
  ⟨(map_continuous _).measurable, map_normOneSplitting_eq_prod w⟩

theorem integral_ideleMeasure_eq_integral_normOne {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (w : InfinitePlace K) {f : IdeleGroup K → E}
    (hf : Integrable f (ideleMeasure K)) :
    ∫ x, f x ∂ideleMeasure K =
      ∫ t, ∫ u, f ((u : IdeleGroup K) * moduleSection w t) ∂normOneMeasure K ∂posRealMeasure := by
  have hcomp : (fun p ↦ f ((normOneSplitting w).symm p)) ∘ (normOneSplitting w) = f :=
    funext fun x ↦ congrArg f ((normOneSplitting w).symm_apply_apply x)
  have h1 : ∫ x, f x ∂ideleMeasure K =
      ∫ p, f ((normOneSplitting w).symm p) ∂(normOneMeasure K).prod posRealMeasure := by
    rw [← map_normOneSplitting_eq_prod w]
    change _ = ∫ p, f ((normOneSplitting w).symm p)
      ∂Measure.map (normOneSplitting w).toHomeomorph.toMeasurableEquiv (ideleMeasure K)
    rw [integral_map_equiv (normOneSplitting w).toHomeomorph.toMeasurableEquiv]
    exact congrArg (fun g ↦ ∫ x, g x ∂ideleMeasure K) hcomp.symm
  rw [h1, integral_prod_symm]
  · rfl
  · rw [← map_normOneSplitting_eq_prod w]
    exact (integrable_map_equiv (normOneSplitting w).toHomeomorph.toMeasurableEquiv
      (fun p ↦ f ((normOneSplitting w).symm p))).2 (by convert hf using 1; exact hcomp)

end Canonical

end

end GroundTheory.Global
