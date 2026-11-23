import Mathlib
import GroundTheory.AutomorphicForms.RealIwasawaUnipotentHaar

namespace GroundTheory.Automorphic

open Matrix Set MeasureTheory Measure
open scoped ComplexOrder NNReal ENNReal

set_option linter.unusedSectionVars false

section Unimodular

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
  [BorelSpace G] [LocallyCompactSpace G] [SecondCountableTopology G]

theorem isInvInvariant_of_isMulRightInvariant (μ : Measure G) [μ.IsHaarMeasure]
    [μ.IsMulRightInvariant] : μ.IsInvInvariant := by
  constructor
  let c : ℝ≥0∞ := haarScalarFactor μ.inv μ
  have hc : μ.inv = c • μ := by
    have := isMulLeftInvariant_eq_smul μ.inv μ
    rwa [ENNReal.smul_def] at this
  have μeq : μ = c ^ 2 • μ := by
    conv_lhs => rw [← Measure.inv_inv μ]
    rw [hc, Measure.inv_def (c • μ), Measure.map_smul, ← Measure.inv_def, hc, smul_smul, pow_two]
  have K : TopologicalSpace.PositiveCompacts G := Classical.arbitrary _
  have h1 : c ^ 2 * μ K = 1 ^ 2 * μ K := by
    conv_rhs => rw [μeq]
    simp
  have h2 : c ^ 2 = 1 ^ 2 :=
    (ENNReal.mul_left_inj (measure_pos_of_nonempty_interior _ K.interior_nonempty).ne'
          K.isCompact.measure_lt_top.ne).1 h1
  have h3 : c = 1 := (ENNReal.pow_right_strictMono two_ne_zero).injective h2
  rw [hc, h3, one_smul]

theorem isMulRightInvariant_of_compactSpace [CompactSpace G] (μ : Measure G) [μ.IsHaarMeasure] :
    μ.IsMulRightInvariant := by
  constructor
  intro g
  have hfin : IsFiniteMeasureOnCompacts (map (· * g) μ) :=
    IsFiniteMeasureOnCompacts.map μ (Homeomorph.mulRight g)
  have h := isMulLeftInvariant_eq_smul (map (· * g) μ) μ
  set c := haarScalarFactor (map (· * g) μ) μ
  have hu := congrArg (fun ν : Measure G => ν univ) h
  simp only [map_apply (measurable_mul_const g) MeasurableSet.univ, preimage_univ,
    Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at hu
  have hpos : μ univ ≠ 0 := IsOpenPosMeasure.open_pos univ isOpen_univ univ_nonempty
  have htop : μ univ ≠ ∞ := isCompact_univ.measure_lt_top.ne
  have hc : (c : ℝ≥0∞) = 1 := by
    have := (ENNReal.mul_left_inj hpos htop).1 (hu.symm.trans (one_mul _).symm)
    exact this
  rw [h, ENNReal.smul_def, hc, one_smul]

end Unimodular

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [LinearOrder n]

section Abelian

theorem diagPos_mul_comm (a b : diagPosSubgroup n 𝕜) : a * b = b * a := by
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul]
  rw [eq_diagonal_of_mem_diagPos a.2, eq_diagonal_of_mem_diagPos b.2, diagonal_mul_diagonal,
    diagonal_mul_diagonal]
  congr 1
  funext i
  ring

variable [MeasurableSpace (GL n 𝕜)] [BorelSpace (GL n 𝕜)]

instance isMulRightInvariant_diagPos (μ : Measure (diagPosSubgroup n 𝕜)) [μ.IsHaarMeasure] :
    μ.IsMulRightInvariant :=
  ⟨fun g => by
    have e : (fun x : diagPosSubgroup n 𝕜 => x * g) = (fun x => g * x) :=
      funext fun x => diagPos_mul_comm x g
    rw [e, map_mul_left_eq_self]⟩

theorem continuous_iwasawaDelta_diagPos_ennreal :
    Continuous (fun a : diagPosSubgroup n 𝕜 => (iwasawaDelta (a : GL n 𝕜) : ℝ≥0∞)) :=
  ENNReal.continuous_coe.comp continuous_iwasawaDelta_diagPos

theorem measurable_iwasawaDelta_diagPos :
    Measurable (fun a : diagPosSubgroup n 𝕜 => (iwasawaDelta (a : GL n 𝕜) : ℝ≥0∞)) :=
  continuous_iwasawaDelta_diagPos_ennreal.measurable

theorem iwasawaDelta_diagPos_mul (a b : diagPosSubgroup n 𝕜) :
    iwasawaDelta ((a * b : diagPosSubgroup n 𝕜) : GL n 𝕜) =
      iwasawaDelta (a : GL n 𝕜) * iwasawaDelta (b : GL n 𝕜) :=
  iwasawaDelta_mul (diagPosSubgroup_le_upperPosSubgroup a.2).1
    (diagPosSubgroup_le_upperPosSubgroup b.2).1

theorem iwasawaDelta_diagPos_ne_zero (a : diagPosSubgroup n 𝕜) : iwasawaDelta (a : GL n 𝕜) ≠ 0 :=
  iwasawaDelta_ne_zero (diagPosSubgroup_le_upperPosSubgroup a.2)

instance isFiniteMeasureOnCompacts_withDensity_iwasawaDelta (μ : Measure (diagPosSubgroup n 𝕜))
    [IsFiniteMeasureOnCompacts μ] :
    IsFiniteMeasureOnCompacts (μ.withDensity fun a => (iwasawaDelta (a : GL n 𝕜) : ℝ≥0∞)) :=
  ⟨fun K hK => by
    rw [withDensity_apply _ hK.measurableSet]
    exact setLIntegral_lt_top_of_isCompact hK.measure_lt_top.ne hK continuous_iwasawaDelta_diagPos⟩

theorem map_mul_right_withDensity_iwasawaDelta (μ : Measure (diagPosSubgroup n 𝕜))
    [μ.IsHaarMeasure] (a' : diagPosSubgroup n 𝕜) :
    map (· * a') (μ.withDensity fun a => (iwasawaDelta (a : GL n 𝕜) : ℝ≥0∞)) =
      (iwasawaDelta ((a'⁻¹ : diagPosSubgroup n 𝕜) : GL n 𝕜) : ℝ≥0∞) •
        μ.withDensity fun a => (iwasawaDelta (a : GL n 𝕜) : ℝ≥0∞) := by
  ext s hs
  rw [map_apply (measurable_mul_const a') hs, withDensity_apply _ (measurable_mul_const a' hs),
    Measure.smul_apply, withDensity_apply _ hs, smul_eq_mul,
    ← lintegral_indicator (measurable_mul_const a' hs), ← lintegral_indicator hs]
  have e : ∀ a : diagPosSubgroup n 𝕜,
      ((· * a') ⁻¹' s).indicator (fun a => (iwasawaDelta (a : GL n 𝕜) : ℝ≥0∞)) a =
        s.indicator (fun x => (iwasawaDelta ((x * a'⁻¹ : diagPosSubgroup n 𝕜) : GL n 𝕜) : ℝ≥0∞))
          (a * a') := by
    intro a
    by_cases h : a * a' ∈ s
    · rw [indicator_of_mem (show a ∈ (· * a') ⁻¹' s from h), indicator_of_mem h, mul_inv_cancel_right]
    · rw [indicator_of_notMem (show a ∉ (· * a') ⁻¹' s from h), indicator_of_notMem h]
  simp_rw [e]
  rw [lintegral_mul_right_eq_self (fun x => s.indicator (fun x =>
    (iwasawaDelta ((x * a'⁻¹ : diagPosSubgroup n 𝕜) : GL n 𝕜) : ℝ≥0∞)) x) a']
  rw [← lintegral_const_mul _ ((measurable_iwasawaDelta_diagPos).indicator hs)]
  congr 1
  funext x
  by_cases hx : x ∈ s
  · simp only [indicator_of_mem hx, iwasawaDelta_diagPos_mul, ENNReal.coe_mul]
    ring
  · simp [indicator_of_notMem hx]

end Abelian

section Borel

variable [WellFoundedLT n] [LocallyFiniteOrderBot n] [MeasurableSpace (GL n 𝕜)]
  [BorelSpace (GL n 𝕜)]

theorem measurable_diagUnipotentMul :
    Measurable (diagUnipotentMul : diagPosSubgroup n 𝕜 × upperUnipotentSubgroup n 𝕜 →
      upperPosSubgroup n 𝕜) :=
  (diagUnipotentHomeomorph (𝕜 := 𝕜) (n := n)).continuous.measurable

theorem continuous_diagConj_inv_left (u' : upperUnipotentSubgroup n 𝕜) :
    Continuous fun a : diagPosSubgroup n 𝕜 => diagConj a⁻¹ u' := by
  refine continuous_induced_rng.2 ?_
  have h1 : Continuous fun a : diagPosSubgroup n 𝕜 => ((a⁻¹ : diagPosSubgroup n 𝕜) : GL n 𝕜) :=
    continuous_subtype_val.comp continuous_inv
  exact (h1.mul continuous_const).mul h1.inv

theorem isMulLeftInvariant_map_diagUnipotentMul (μA : Measure (diagPosSubgroup n 𝕜))
    [μA.IsHaarMeasure] (μN : Measure (upperUnipotentSubgroup n 𝕜)) [μN.IsHaarMeasure] :
    (map diagUnipotentMul (μA.prod μN)).IsMulLeftInvariant := by
  constructor
  intro b
  obtain ⟨⟨a', u'⟩, rfl⟩ := diagUnipotentHomeomorph.surjective b
  let S : diagPosSubgroup n 𝕜 × upperUnipotentSubgroup n 𝕜 →
      diagPosSubgroup n 𝕜 × upperUnipotentSubgroup n 𝕜 :=
    fun p => (a' * p.1, diagConj p.1⁻¹ u' * p.2)
  have hS : Measurable S :=
    ((continuous_const.mul continuous_fst).prodMk
      (((continuous_diagConj_inv_left u').comp continuous_fst).mul continuous_snd)).measurable
  have e : (fun x => diagUnipotentHomeomorph (a', u') * x) ∘ diagUnipotentMul =
      diagUnipotentMul ∘ S := by
    funext p
    apply Subtype.ext
    simp only [Function.comp_apply, diagUnipotentHomeomorph_apply, Subgroup.coe_mul,
      coe_diagUnipotentMul, coe_diagConj, Subgroup.coe_inv, S]
    group
  have hP : map S (μA.prod μN) = μA.prod μN := by
    ext s hs
    rw [map_apply hS hs, prod_apply (hS hs), prod_apply hs]
    have e2 : ∀ a, Prod.mk a ⁻¹' (S ⁻¹' s) =
        (fun u => diagConj a⁻¹ u' * u) ⁻¹' (Prod.mk (a' * a) ⁻¹' s) := fun a => rfl
    simp_rw [e2, measure_preimage_mul]
    exact lintegral_mul_left_eq_self (fun a => μN (Prod.mk a ⁻¹' s)) a'
  rw [map_map (measurable_const_mul _) measurable_diagUnipotentMul, e,
    ← map_map measurable_diagUnipotentMul hS, hP]

theorem exists_map_diagUnipotentMul_eq_smul (μA : Measure (diagPosSubgroup n 𝕜))
    [μA.IsHaarMeasure] (μN : Measure (upperUnipotentSubgroup n 𝕜)) [μN.IsHaarMeasure]
    (μB : Measure (upperPosSubgroup n 𝕜)) [μB.IsHaarMeasure] :
    ∃ c : ℝ≥0, c ≠ 0 ∧ map diagUnipotentMul (μA.prod μN) = c • μB := by
  haveI := isMulLeftInvariant_map_diagUnipotentMul μA μN
  haveI : IsFiniteMeasureOnCompacts (map diagUnipotentMul (μA.prod μN)) :=
    IsFiniteMeasureOnCompacts.map (μA.prod μN) diagUnipotentHomeomorph
  refine ⟨haarScalarFactor (map diagUnipotentMul (μA.prod μN)) μB, ?_,
    isMulLeftInvariant_eq_smul _ _⟩
  intro h0
  have h := isMulLeftInvariant_eq_smul (map diagUnipotentMul (μA.prod μN)) μB
  rw [h0, zero_smul] at h
  have hu := congrArg (fun ν : Measure (upperPosSubgroup n 𝕜) => ν univ) h
  simp only [map_apply measurable_diagUnipotentMul MeasurableSet.univ, preimage_univ,
    ← univ_prod_univ, prod_prod, Measure.coe_zero, Pi.zero_apply, mul_eq_zero] at hu
  rcases hu with hu | hu
  · exact IsOpenPosMeasure.open_pos (μ := μA) univ isOpen_univ univ_nonempty hu
  · exact IsOpenPosMeasure.open_pos (μ := μN) univ isOpen_univ univ_nonempty hu

theorem lintegral_upperPos_eq (μA : Measure (diagPosSubgroup n 𝕜)) [μA.IsHaarMeasure]
    (μN : Measure (upperUnipotentSubgroup n 𝕜)) [μN.IsHaarMeasure]
    (μB : Measure (upperPosSubgroup n 𝕜)) [μB.IsHaarMeasure] :
    ∃ c : ℝ≥0, c ≠ 0 ∧ ∀ f : upperPosSubgroup n 𝕜 → ℝ≥0∞, Measurable f →
      ∫⁻ b, f b ∂μB = c * ∫⁻ a, ∫⁻ u, f (diagUnipotentMul (a, u)) ∂μN ∂μA := by
  obtain ⟨c, hc, h⟩ := exists_map_diagUnipotentMul_eq_smul μA μN μB
  refine ⟨c⁻¹, inv_ne_zero hc, fun f hf => ?_⟩
  have hB : μB = c⁻¹ • map diagUnipotentMul (μA.prod μN) := by
    rw [h, smul_smul, inv_mul_cancel₀ hc, one_smul]
  rw [hB, lintegral_smul_measure, lintegral_map hf measurable_diagUnipotentMul,
    lintegral_prod (fun p => f (diagUnipotentMul p))
      (hf.comp measurable_diagUnipotentMul).aemeasurable, ENNReal.smul_def,
    smul_eq_mul]

theorem isMulRightInvariant_map_diagUnipotentMul_withDensity
    (μA : Measure (diagPosSubgroup n 𝕜)) [μA.IsHaarMeasure]
    (μN : Measure (upperUnipotentSubgroup n 𝕜)) [μN.IsHaarMeasure] :
    (map diagUnipotentMul ((μA.withDensity fun a => (iwasawaDelta (a : GL n 𝕜) : ℝ≥0∞)).prod
      μN)).IsMulRightInvariant := by
  constructor
  intro b
  obtain ⟨⟨a', u'⟩, rfl⟩ := diagUnipotentHomeomorph.surjective b
  set ρ := μA.withDensity fun a => (iwasawaDelta (a : GL n 𝕜) : ℝ≥0∞)
  let φ : upperUnipotentSubgroup n 𝕜 → upperUnipotentSubgroup n 𝕜 := fun u => diagConj a'⁻¹ u * u'
  have hφ : Measurable φ := ((continuous_diagConj _).mul continuous_const).measurable
  have e : (fun x => x * diagUnipotentHomeomorph (a', u')) ∘ diagUnipotentMul =
      diagUnipotentMul ∘ Prod.map (· * a') φ := by
    funext p
    apply Subtype.ext
    simp only [Function.comp_apply, diagUnipotentHomeomorph_apply, Subgroup.coe_mul,
      coe_diagUnipotentMul, coe_diagConj, Subgroup.coe_inv, Prod.map_fst, Prod.map_snd, φ]
    group
  have hφμ : map φ μN = ((iwasawaDelta ((a'⁻¹ : diagPosSubgroup n 𝕜) : GL n 𝕜) : ℝ≥0∞))⁻¹ • μN := by
    have e2 : φ = (· * u') ∘ diagConj a'⁻¹ := rfl
    rw [e2, ← map_map (measurable_mul_const u') (continuous_diagConj _).measurable,
      map_diagConj_haar, Measure.map_smul, map_mul_right_eq_self]
  have hδ0 : (iwasawaDelta ((a'⁻¹ : diagPosSubgroup n 𝕜) : GL n 𝕜) : ℝ≥0∞) ≠ 0 :=
    ENNReal.coe_ne_zero.2 (iwasawaDelta_diagPos_ne_zero _)
  have hδt : (iwasawaDelta ((a'⁻¹ : diagPosSubgroup n 𝕜) : GL n 𝕜) : ℝ≥0∞) ≠ ∞ :=
    ENNReal.coe_ne_top
  rw [map_map (measurable_mul_const _) measurable_diagUnipotentMul, e,
    ← map_map measurable_diagUnipotentMul ((measurable_mul_const a').prodMap hφ),
    ← map_prod_map _ _ (measurable_mul_const a') hφ, map_mul_right_withDensity_iwasawaDelta, hφμ,
    prod_smul_left, prod_smul_right, smul_smul, ENNReal.mul_inv_cancel hδ0 hδt, one_smul]

theorem exists_map_diagUnipotentMul_withDensity_eq_smul_inv
    (μA : Measure (diagPosSubgroup n 𝕜)) [μA.IsHaarMeasure]
    (μN : Measure (upperUnipotentSubgroup n 𝕜)) [μN.IsHaarMeasure]
    (μB : Measure (upperPosSubgroup n 𝕜)) [μB.IsHaarMeasure] :
    ∃ c : ℝ≥0, c ≠ 0 ∧ map diagUnipotentMul ((μA.withDensity fun a =>
      (iwasawaDelta (a : GL n 𝕜) : ℝ≥0∞)).prod μN) = c • μB.inv := by
  set ρ := μA.withDensity fun a => (iwasawaDelta (a : GL n 𝕜) : ℝ≥0∞) with hρ
  set lam := map diagUnipotentMul (ρ.prod μN) with hlam
  haveI : lam.IsMulRightInvariant := isMulRightInvariant_map_diagUnipotentMul_withDensity μA μN
  haveI : IsFiniteMeasureOnCompacts lam := IsFiniteMeasureOnCompacts.map (ρ.prod μN)
    diagUnipotentHomeomorph
  have h := isMulLeftInvariant_eq_smul lam.inv μB
  set c := haarScalarFactor lam.inv μB
  have key : lam = c • μB.inv := by
    rw [← Measure.inv_inv lam, h, Measure.inv_def (c • μB), Measure.map_smul, ← Measure.inv_def]
  refine ⟨c, ?_, key⟩
  intro h0
  rw [h0, zero_smul] at key
  have hu := congrArg (fun ν : Measure (upperPosSubgroup n 𝕜) => ν univ) key
  simp only [lam, map_apply measurable_diagUnipotentMul MeasurableSet.univ, preimage_univ,
    ← univ_prod_univ, prod_prod, Measure.coe_zero, Pi.zero_apply, mul_eq_zero] at hu
  rcases hu with hu | hu
  · rw [hρ, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      lintegral_eq_zero_iff measurable_iwasawaDelta_diagPos] at hu
    have : μA {a | (iwasawaDelta (a : GL n 𝕜) : ℝ≥0∞) ≠ 0} = 0 := ae_iff.1 hu
    have e : {a : diagPosSubgroup n 𝕜 | (iwasawaDelta (a : GL n 𝕜) : ℝ≥0∞) ≠ 0} = univ :=
      eq_univ_of_forall fun a => ENNReal.coe_ne_zero.2 (iwasawaDelta_diagPos_ne_zero a)
    rw [e] at this
    exact IsOpenPosMeasure.open_pos (μ := μA) univ isOpen_univ univ_nonempty this
  · exact IsOpenPosMeasure.open_pos (μ := μN) univ isOpen_univ univ_nonempty hu

theorem lintegral_inv_upperPos_eq (μA : Measure (diagPosSubgroup n 𝕜)) [μA.IsHaarMeasure]
    (μN : Measure (upperUnipotentSubgroup n 𝕜)) [μN.IsHaarMeasure]
    (μB : Measure (upperPosSubgroup n 𝕜)) [μB.IsHaarMeasure] :
    ∃ c : ℝ≥0, c ≠ 0 ∧ ∀ f : upperPosSubgroup n 𝕜 → ℝ≥0∞, Measurable f →
      ∫⁻ b, f b ∂μB.inv =
        c * ∫⁻ a, (iwasawaDelta (a : GL n 𝕜) : ℝ≥0∞) * ∫⁻ u, f (diagUnipotentMul (a, u)) ∂μN ∂μA := by
  obtain ⟨c, hc, h⟩ := exists_map_diagUnipotentMul_withDensity_eq_smul_inv μA μN μB
  refine ⟨c⁻¹, inv_ne_zero hc, fun f hf => ?_⟩
  have hB : μB.inv = c⁻¹ • map diagUnipotentMul ((μA.withDensity fun a =>
      (iwasawaDelta (a : GL n 𝕜) : ℝ≥0∞)).prod μN) := by
    rw [h, smul_smul, inv_mul_cancel₀ hc, one_smul]
  have hm := hf.comp measurable_diagUnipotentMul
  rw [hB, lintegral_smul_measure, lintegral_map hf measurable_diagUnipotentMul,
    lintegral_prod (fun p => f (diagUnipotentMul p)) hm.aemeasurable,
    lintegral_withDensity_eq_lintegral_mul _ measurable_iwasawaDelta_diagPos
      (g := fun a => ∫⁻ u, f (diagUnipotentMul (a, u)) ∂μN) hm.lintegral_prod_right',
    ENNReal.smul_def, smul_eq_mul]
  rfl

theorem lintegral_inv_upperPos_eq_delta (μB : Measure (upperPosSubgroup n 𝕜))
    [μB.IsHaarMeasure] :
    ∃ c : ℝ≥0, c ≠ 0 ∧ ∀ f : upperPosSubgroup n 𝕜 → ℝ≥0∞, Measurable f →
      ∫⁻ b, f b ∂μB.inv = c * ∫⁻ b, (iwasawaDelta (b : GL n 𝕜) : ℝ≥0∞) * f b ∂μB := by
  let μA : Measure (diagPosSubgroup n 𝕜) := Measure.haar
  let μN : Measure (upperUnipotentSubgroup n 𝕜) := Measure.haar
  obtain ⟨c1, hc1, h1⟩ := lintegral_upperPos_eq μA μN μB
  obtain ⟨c2, hc2, h2⟩ := lintegral_inv_upperPos_eq μA μN μB
  refine ⟨c2 * c1⁻¹, mul_ne_zero hc2 (inv_ne_zero hc1), fun f hf => ?_⟩
  have hδB : Measurable fun b : upperPosSubgroup n 𝕜 => (iwasawaDelta (b : GL n 𝕜) : ℝ≥0∞) := by
    have e : (fun b : upperPosSubgroup n 𝕜 => (iwasawaDelta (b : GL n 𝕜) : ℝ≥0∞)) =
        (fun a : diagPosSubgroup n 𝕜 => (iwasawaDelta (a : GL n 𝕜) : ℝ≥0∞)) ∘ upperPosDiagPart := by
      funext b
      simp only [Function.comp_apply]
      conv_lhs => rw [← diagUnipotentMul_parts b]
      rw [iwasawaDelta_diagUnipotentMul]
    rw [e]
    exact measurable_iwasawaDelta_diagPos.comp continuous_upperPosDiagPart.measurable
  rw [h2 f hf, h1 (fun b => (iwasawaDelta (b : GL n 𝕜) : ℝ≥0∞) * f b) (hδB.mul hf)]
  simp_rw [iwasawaDelta_diagUnipotentMul]
  have hinner : ∀ a : diagPosSubgroup n 𝕜,
      ∫⁻ u, (iwasawaDelta (a : GL n 𝕜) : ℝ≥0∞) * f (diagUnipotentMul (a, u)) ∂μN =
        (iwasawaDelta (a : GL n 𝕜) : ℝ≥0∞) * ∫⁻ u, f (diagUnipotentMul (a, u)) ∂μN :=
    fun a => lintegral_const_mul' _ _ ENNReal.coe_ne_top
  simp_rw [hinner]
  rw [ENNReal.coe_mul, mul_assoc, ← mul_assoc ((c1⁻¹ : ℝ≥0) : ℝ≥0∞), ← ENNReal.coe_mul,
    inv_mul_cancel₀ hc1, ENNReal.coe_one, one_mul]

end Borel

section KAN

instance secondCountableTopology_matrix_rclike : SecondCountableTopology (Matrix n n 𝕜) :=
  inferInstanceAs (SecondCountableTopology (n → n → 𝕜))

instance locallyCompactSpace_matrix_rclike : LocallyCompactSpace (Matrix n n 𝕜) :=
  inferInstanceAs (LocallyCompactSpace (n → n → 𝕜))

instance secondCountableTopology_unitaryGroup : SecondCountableTopology (unitaryGroup n 𝕜) :=
  TopologicalSpace.Subtype.secondCountableTopology _

theorem continuous_unitary_toUnits :
    Continuous (fun k : unitaryGroup n 𝕜 => Unitary.toUnits k) :=
  Units.continuous_iff.2 ⟨continuous_subtype_val, continuous_subtype_val.star⟩

variable [WellFoundedLT n] [LocallyFiniteOrderBot n] [MeasurableSpace (GL n 𝕜)]
  [BorelSpace (GL n 𝕜)]

theorem lintegral_KAN_of_KB {μG : Measure (GL n 𝕜)} [MeasurableSpace (unitaryGroup n 𝕜)]
    {μK : Measure (unitaryGroup n 𝕜)}
    (μA : Measure (diagPosSubgroup n 𝕜)) [μA.IsHaarMeasure]
    (μN : Measure (upperUnipotentSubgroup n 𝕜)) [μN.IsHaarMeasure]
    (μB : Measure (upperPosSubgroup n 𝕜)) [μB.IsHaarMeasure]
    (hKB : ∃ c : ℝ≥0, c ≠ 0 ∧ ∀ f : GL n 𝕜 → ℝ≥0∞, Measurable f →
      ∫⁻ g, f g ∂μG = c * ∫⁻ k, ∫⁻ b, f (Unitary.toUnits k * b) ∂μB.inv ∂μK) :
    ∃ c : ℝ≥0, c ≠ 0 ∧ ∀ f : GL n 𝕜 → ℝ≥0∞, Measurable f →
      ∫⁻ g, f g ∂μG = c * ∫⁻ k, ∫⁻ a, (iwasawaDelta (a : GL n 𝕜) : ℝ≥0∞) *
        ∫⁻ u, f (Unitary.toUnits k * a * u) ∂μN ∂μA ∂μK := by
  obtain ⟨c, hc, h⟩ := hKB
  obtain ⟨c2, hc2, h2⟩ := lintegral_inv_upperPos_eq μA μN μB
  refine ⟨c * c2, mul_ne_zero hc hc2, fun f hf => ?_⟩
  rw [h f hf]
  have hk : ∀ k : unitaryGroup n 𝕜, ∫⁻ b, f (Unitary.toUnits k * b) ∂μB.inv =
      c2 * ∫⁻ a, (iwasawaDelta (a : GL n 𝕜) : ℝ≥0∞) *
        ∫⁻ u, f (Unitary.toUnits k * a * u) ∂μN ∂μA := by
    intro k
    rw [h2 (fun b : upperPosSubgroup n 𝕜 => f (Unitary.toUnits k * b))
      (hf.comp ((measurable_const_mul _).comp measurable_subtype_coe))]
    simp only [coe_diagUnipotentMul, mul_assoc]
  rw [lintegral_congr hk, lintegral_const_mul' _ _ ENNReal.coe_ne_top, ENNReal.coe_mul, mul_assoc]

theorem lintegral_ANK_of_KB {μG : Measure (GL n 𝕜)} [μG.IsInvInvariant]
    [MeasurableSpace (unitaryGroup n 𝕜)] [BorelSpace (unitaryGroup n 𝕜)]
    {μK : Measure (unitaryGroup n 𝕜)} [SFinite μK] [μK.IsInvInvariant]
    (μA : Measure (diagPosSubgroup n 𝕜)) [μA.IsHaarMeasure]
    (μN : Measure (upperUnipotentSubgroup n 𝕜)) [μN.IsHaarMeasure]
    (μB : Measure (upperPosSubgroup n 𝕜)) [μB.IsHaarMeasure]
    (hKB : ∃ c : ℝ≥0, c ≠ 0 ∧ ∀ f : GL n 𝕜 → ℝ≥0∞, Measurable f →
      ∫⁻ g, f g ∂μG = c * ∫⁻ k, ∫⁻ b, f (Unitary.toUnits k * b) ∂μB.inv ∂μK) :
    ∃ c : ℝ≥0, c ≠ 0 ∧ ∀ f : GL n 𝕜 → ℝ≥0∞, Measurable f →
      ∫⁻ g, f g ∂μG = c * ∫⁻ a, ∫⁻ u, ∫⁻ k, f (a * u * Unitary.toUnits k) ∂μK ∂μN ∂μA := by
  obtain ⟨c, hc, h⟩ := hKB
  obtain ⟨c1, hc1, h1⟩ := lintegral_upperPos_eq μA μN μB
  refine ⟨c * c1, mul_ne_zero hc hc1, fun f hf => ?_⟩
  have hmF : Measurable fun p : upperPosSubgroup n 𝕜 × unitaryGroup n 𝕜 =>
      f ((p.1 : GL n 𝕜) * Unitary.toUnits p.2) :=
    hf.comp ((continuous_subtype_val.comp continuous_fst).mul
      (continuous_unitary_toUnits.comp continuous_snd)).measurable
  have hmF' : Measurable fun p : unitaryGroup n 𝕜 × upperPosSubgroup n 𝕜 =>
      f ((p.2 : GL n 𝕜) * (Unitary.toUnits p.1)⁻¹) :=
    hf.comp ((continuous_subtype_val.comp continuous_snd).mul
      (continuous_unitary_toUnits.comp continuous_fst).inv).measurable
  rw [← lintegral_inv_eq_self (μ := μG) f, h (fun g => f g⁻¹) (hf.comp measurable_inv)]
  have step2 : ∀ k : unitaryGroup n 𝕜,
      ∫⁻ b, f ((Unitary.toUnits k * (b : GL n 𝕜))⁻¹) ∂μB.inv =
        ∫⁻ b, f ((b : GL n 𝕜) * (Unitary.toUnits k)⁻¹) ∂μB := by
    intro k
    rw [Measure.inv_def, lintegral_map _ measurable_inv]
    · simp only [Subgroup.coe_inv, _root_.mul_inv_rev, inv_inv]
    · exact hf.comp (measurable_inv.comp ((measurable_const_mul _).comp measurable_subtype_coe))
  rw [lintegral_congr step2, lintegral_lintegral_swap hmF'.aemeasurable]
  have step3 : ∀ b : upperPosSubgroup n 𝕜,
      ∫⁻ k, f ((b : GL n 𝕜) * (Unitary.toUnits k)⁻¹) ∂μK =
        ∫⁻ k, f ((b : GL n 𝕜) * Unitary.toUnits k) ∂μK := by
    intro b
    have := lintegral_inv_eq_self (μ := μK) (fun k => f ((b : GL n 𝕜) * Unitary.toUnits k))
    simpa only [map_inv] using this
  rw [lintegral_congr step3, h1 _ hmF.lintegral_prod_right']
  simp only [coe_diagUnipotentMul]
  rw [ENNReal.coe_mul, mul_assoc]

end KAN

section Real

variable [WellFoundedLT n] [LocallyFiniteOrderBot n]

theorem exists_eq_smul_haarGLReal (μG : Measure (GL n ℝ)) [μG.IsHaarMeasure] :
    ∃ s : ℝ≥0, s ≠ 0 ∧ μG = s • haarGLReal (Measure.addHaar : Measure (Matrix n n ℝ)) :=
  ⟨_, (haarScalarFactor_pos_of_isHaarMeasure _ _).ne', isMulLeftInvariant_eq_smul _ _⟩

theorem lintegral_GLReal_KAN (μG : Measure (GL n ℝ)) [μG.IsHaarMeasure]
    (μK : Measure (unitaryGroup n ℝ)) [μK.IsHaarMeasure]
    (μA : Measure (diagPosSubgroup n ℝ)) [μA.IsHaarMeasure]
    (μN : Measure (upperUnipotentSubgroup n ℝ)) [μN.IsHaarMeasure] :
    ∃ c : ℝ≥0, c ≠ 0 ∧ ∀ f : GL n ℝ → ℝ≥0∞, Measurable f →
      ∫⁻ g, f g ∂μG = c * ∫⁻ k, ∫⁻ a, (iwasawaDelta (a : GL n ℝ) : ℝ≥0∞) *
        ∫⁻ u, f (Unitary.toUnits k * a * u) ∂μN ∂μA ∂μK := by
  obtain ⟨s, hs, hG⟩ := exists_eq_smul_haarGLReal μG
  let μB : Measure (upperPosSubgroup n ℝ) := Measure.haar
  obtain ⟨c, hc, h⟩ := lintegral_haarGLReal_iwasawa
    (Measure.addHaar : Measure (Matrix n n ℝ)) μK μB
  refine lintegral_KAN_of_KB μA μN μB ⟨s * c, mul_ne_zero hs hc, fun f hf => ?_⟩
  rw [hG, lintegral_smul_measure, h f hf, ENNReal.smul_def, smul_eq_mul, ENNReal.coe_mul, mul_assoc]

theorem lintegral_GLReal_ANK (μG : Measure (GL n ℝ)) [μG.IsHaarMeasure]
    (μK : Measure (unitaryGroup n ℝ)) [μK.IsHaarMeasure]
    (μA : Measure (diagPosSubgroup n ℝ)) [μA.IsHaarMeasure]
    (μN : Measure (upperUnipotentSubgroup n ℝ)) [μN.IsHaarMeasure] :
    ∃ c : ℝ≥0, c ≠ 0 ∧ ∀ f : GL n ℝ → ℝ≥0∞, Measurable f →
      ∫⁻ g, f g ∂μG = c * ∫⁻ a, ∫⁻ u, ∫⁻ k, f (a * u * Unitary.toUnits k) ∂μK ∂μN ∂μA := by
  obtain ⟨s, hs, hG⟩ := exists_eq_smul_haarGLReal μG
  haveI : μG.IsMulRightInvariant := by rw [hG]; infer_instance
  haveI := isInvInvariant_of_isMulRightInvariant μG
  haveI := isMulRightInvariant_of_compactSpace μK
  haveI := isInvInvariant_of_isMulRightInvariant μK
  let μB : Measure (upperPosSubgroup n ℝ) := Measure.haar
  obtain ⟨c, hc, h⟩ := lintegral_haarGLReal_iwasawa
    (Measure.addHaar : Measure (Matrix n n ℝ)) μK μB
  refine lintegral_ANK_of_KB μA μN μB ⟨s * c, mul_ne_zero hs hc, fun f hf => ?_⟩
  rw [hG, lintegral_smul_measure, h f hf, ENNReal.smul_def, smul_eq_mul, ENNReal.coe_mul, mul_assoc]

end Real

section Complex

variable [WellFoundedLT n] [LocallyFiniteOrderBot n]

theorem exists_eq_smul_haarGLComplex (μG : Measure (GL n ℂ)) [μG.IsHaarMeasure] :
    ∃ s : ℝ≥0, s ≠ 0 ∧ μG = s • haarGLComplex (Measure.addHaar : Measure (Matrix n n ℂ)) :=
  ⟨_, (haarScalarFactor_pos_of_isHaarMeasure _ _).ne', isMulLeftInvariant_eq_smul _ _⟩

theorem lintegral_GLComplex_KAN (μG : Measure (GL n ℂ)) [μG.IsHaarMeasure]
    (μK : Measure (unitaryGroup n ℂ)) [μK.IsHaarMeasure]
    (μA : Measure (diagPosSubgroup n ℂ)) [μA.IsHaarMeasure]
    (μN : Measure (upperUnipotentSubgroup n ℂ)) [μN.IsHaarMeasure] :
    ∃ c : ℝ≥0, c ≠ 0 ∧ ∀ f : GL n ℂ → ℝ≥0∞, Measurable f →
      ∫⁻ g, f g ∂μG = c * ∫⁻ k, ∫⁻ a, (iwasawaDelta (a : GL n ℂ) : ℝ≥0∞) *
        ∫⁻ u, f (Unitary.toUnits k * a * u) ∂μN ∂μA ∂μK := by
  obtain ⟨s, hs, hG⟩ := exists_eq_smul_haarGLComplex μG
  let μB : Measure (upperPosSubgroup n ℂ) := Measure.haar
  obtain ⟨c, hc, h⟩ := lintegral_haarGLComplex_iwasawa
    (Measure.addHaar : Measure (Matrix n n ℂ)) μK μB
  refine lintegral_KAN_of_KB μA μN μB ⟨s * c, mul_ne_zero hs hc, fun f hf => ?_⟩
  rw [hG, lintegral_smul_measure, h f hf, ENNReal.smul_def, smul_eq_mul, ENNReal.coe_mul, mul_assoc]

theorem lintegral_GLComplex_ANK (μG : Measure (GL n ℂ)) [μG.IsHaarMeasure]
    (μK : Measure (unitaryGroup n ℂ)) [μK.IsHaarMeasure]
    (μA : Measure (diagPosSubgroup n ℂ)) [μA.IsHaarMeasure]
    (μN : Measure (upperUnipotentSubgroup n ℂ)) [μN.IsHaarMeasure] :
    ∃ c : ℝ≥0, c ≠ 0 ∧ ∀ f : GL n ℂ → ℝ≥0∞, Measurable f →
      ∫⁻ g, f g ∂μG = c * ∫⁻ a, ∫⁻ u, ∫⁻ k, f (a * u * Unitary.toUnits k) ∂μK ∂μN ∂μA := by
  obtain ⟨s, hs, hG⟩ := exists_eq_smul_haarGLComplex μG
  haveI : μG.IsMulRightInvariant := by rw [hG]; infer_instance
  haveI := isInvInvariant_of_isMulRightInvariant μG
  haveI := isMulRightInvariant_of_compactSpace μK
  haveI := isInvInvariant_of_isMulRightInvariant μK
  let μB : Measure (upperPosSubgroup n ℂ) := Measure.haar
  obtain ⟨c, hc, h⟩ := lintegral_haarGLComplex_iwasawa
    (Measure.addHaar : Measure (Matrix n n ℂ)) μK μB
  refine lintegral_ANK_of_KB μA μN μB ⟨s * c, mul_ne_zero hs hc, fun f hf => ?_⟩
  rw [hG, lintegral_smul_measure, h f hf, ENNReal.smul_def, smul_eq_mul, ENNReal.coe_mul, mul_assoc]

end Complex

end GroundTheory.Automorphic
