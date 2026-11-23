import Mathlib
import GroundTheory.LocalFields.LocalFourierSchwartz

noncomputable section

namespace GroundTheory.LocalField

open ValuativeRel MeasureTheory Measure Topology Filter
open scoped WithZero NNReal ENNReal Pointwise

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

section SelfDual

variable [MeasurableSpace K] [BorelSpace K]

def selfDualMeasure (ψ : AddChar K Circle) : Measure K :=
  ((residueCard K : ℝ≥0) ^ ((addCharConductor ψ : ℝ) / 2)) • haarIntegers K

omit [MeasurableSpace K] [BorelSpace K] in
theorem selfDualMeasure_coeff_ne_zero (ψ : AddChar K Circle) :
    ((residueCard K : ℝ≥0) ^ ((addCharConductor ψ : ℝ) / 2)) ≠ 0 :=
  (NNReal.rpow_pos (zero_lt_one.trans one_lt_residueCard_nnreal)).ne'

instance (ψ : AddChar K Circle) : (selfDualMeasure ψ).IsAddHaarMeasure := by
  unfold selfDualMeasure
  exact IsAddHaarMeasure.nnreal_smul (haarIntegers K) (selfDualMeasure_coeff_ne_zero ψ)

theorem selfDualMeasure_integers (ψ : AddChar K Circle) :
    selfDualMeasure ψ (𝒪[K] : Set K) = ((residueCard K : ℝ≥0) ^ ((addCharConductor ψ : ℝ) / 2) : ℝ≥0) := by
  rw [selfDualMeasure, Measure.smul_apply, haarIntegers_integers, ENNReal.smul_def, smul_eq_mul,
    mul_one]

theorem selfDualMeasure_real_valBall_zero (ψ : AddChar K Circle) :
    (selfDualMeasure ψ).real (valBall K 0) = (residueCard K : ℝ) ^ ((addCharConductor ψ : ℝ) / 2) := by
  rw [measureReal_def, coe_valBall_zero, selfDualMeasure_integers, ENNReal.coe_toReal,
    NNReal.coe_rpow, NNReal.coe_natCast]

omit [MeasurableSpace K] [BorelSpace K] in

theorem inversion_const_eq_one_iff (n : ℤ) {r : ℝ} (hr : 0 ≤ r) :
    (residueCard K : ℝ) ^ (-n) * r ^ 2 = 1 ↔ r = (residueCard K : ℝ) ^ ((n : ℝ) / 2) := by
  have hq : (0 : ℝ) < residueCard K := by exact_mod_cast zero_lt_one.trans one_lt_residueCard
  have hsq : ((residueCard K : ℝ) ^ ((n : ℝ) / 2)) ^ 2 = (residueCard K : ℝ) ^ n := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hq.le, ← Real.rpow_intCast]
    congr 1
    push_cast
    ring
  have hne : (residueCard K : ℝ) ^ (-n) ≠ 0 := zpow_ne_zero _ hq.ne'
  constructor
  · intro h
    have h2 : r ^ 2 = (residueCard K : ℝ) ^ n := by
      have := congrArg (fun t => (residueCard K : ℝ) ^ n * t) h
      simp only [mul_one, ← mul_assoc] at this
      rwa [← zpow_add₀ hq.ne', add_neg_cancel, zpow_zero, one_mul] at this
    rw [← hsq] at h2
    exact (pow_left_inj₀ hr (Real.rpow_nonneg hq.le _) two_ne_zero).mp h2
  · intro h
    rw [h, hsq, ← zpow_add₀ hq.ne', neg_add_cancel, zpow_zero]

omit [MeasurableSpace K] [BorelSpace K] in
theorem indicator_valBall_zero_mem_schwartzBruhat :
    (valBall K 0 : Set K).indicator (fun _ => (1 : ℂ)) ∈ schwartzBruhat K := by
  refine ⟨isLocallyConstant_of_add_valBall (N := 0) fun x h hh => ?_, ?_⟩
  · have hiff : x + h ∈ valBall K 0 ↔ x ∈ valBall K 0 :=
      ⟨fun h' => by simpa using sub_mem h' hh, fun h' => add_mem h' hh⟩
    by_cases hx : x ∈ valBall K 0
    · rw [Set.indicator_of_mem (show x + h ∈ (valBall K 0 : Set K) from hiff.mpr hx),
        Set.indicator_of_mem (show x ∈ (valBall K 0 : Set K) from hx)]
    · rw [Set.indicator_of_notMem (show x + h ∉ (valBall K 0 : Set K) from mt hiff.mp hx),
        Set.indicator_of_notMem (show x ∉ (valBall K 0 : Set K) from hx)]
  · exact HasCompactSupport.intro (isCompact_valBall 0) fun x hx => Set.indicator_of_notMem hx _

variable {ψ : AddChar K Circle} (hψ : Continuous ψ) (hψ1 : ψ ≠ 1)
include hψ hψ1

theorem localFourier_localFourier_selfDual {f : K → ℂ} (hf : f ∈ schwartzBruhat K) (x : K) :
    localFourier (selfDualMeasure ψ) ψ (localFourier (selfDualMeasure ψ) ψ f) x = f (-x) := by
  rw [localFourier_localFourier _ hψ hψ1 hf x, selfDualMeasure_real_valBall_zero,
    (inversion_const_eq_one_iff (K := K) (addCharConductor ψ) (Real.rpow_nonneg (Nat.cast_nonneg _) _)).mpr
      rfl]
  simp

def fourierSB (μ : Measure K) [μ.IsAddHaarMeasure] : schwartzBruhat K →ₗ[ℂ] schwartzBruhat K where
  toFun f := ⟨localFourier μ ψ f, localFourier_mem_schwartzBruhat μ hψ hψ1 f.2⟩
  map_add' f g := Subtype.ext <| funext fun y => by
    show ∫ x, ((f : K → ℂ) x + (g : K → ℂ) x) * (ψ (x * y) : ℂ) ∂μ =
      ∫ x, (f : K → ℂ) x * (ψ (x * y) : ℂ) ∂μ + ∫ x, (g : K → ℂ) x * (ψ (x * y) : ℂ) ∂μ
    simp only [add_mul]
    exact integral_add (integrable_mul_char_of_mem_schwartzBruhat μ hψ f.2 y)
      (integrable_mul_char_of_mem_schwartzBruhat μ hψ g.2 y)
  map_smul' c f := Subtype.ext <| funext fun y => by
    show ∫ x, (c * (f : K → ℂ) x) * (ψ (x * y) : ℂ) ∂μ = c * ∫ x, (f : K → ℂ) x * (ψ (x * y) : ℂ) ∂μ
    simp only [mul_assoc]
    exact integral_const_mul c _

end SelfDual

section Multiplicative

variable [MeasurableSpace K] [BorelSpace K]

theorem measurableEmbedding_units_val : MeasurableEmbedding (Units.val : Kˣ → K) where
  injective := Units.val_injective
  measurable := comap_measurable _
  measurableSet_image' := by
    rintro _ ⟨t, ht, rfl⟩
    have : (Units.val : Kˣ → K) '' (Units.val ⁻¹' t) = t ∩ {0}ᶜ := by
      ext x
      constructor
      · rintro ⟨u, hu, rfl⟩
        exact ⟨hu, u.ne_zero⟩
      · rintro ⟨hx, hx0⟩
        exact ⟨Units.mk0 x hx0, hx, rfl⟩
    rw [this]
    exact ht.inter (measurableSet_singleton 0).compl

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [MeasurableSpace K]
  [BorelSpace K] in
theorem range_units_val : Set.range (Units.val : Kˣ → K) = {0}ᶜ := by
  ext x
  constructor
  · rintro ⟨u, rfl⟩
    exact u.ne_zero
  · intro hx
    exact ⟨Units.mk0 x hx, rfl⟩

omit [MeasurableSpace K] [BorelSpace K] in

theorem isOpenEmbedding_units_val : IsOpenEmbedding (Units.val : Kˣ → K) :=
  ⟨Units.isEmbedding_val₀, by rw [range_units_val]; exact isOpen_compl_singleton⟩

variable (K) in

def multHaarConst : ℝ≥0∞ := (1 - ((residueCard K : ℝ≥0∞))⁻¹)⁻¹

omit [MeasurableSpace K] [BorelSpace K] in
theorem one_sub_inv_residueCard_ne_zero : (1 : ℝ≥0∞) - ((residueCard K : ℝ≥0∞))⁻¹ ≠ 0 :=
  (tsub_pos_of_lt (ENNReal.inv_lt_one.mpr (by exact_mod_cast one_lt_residueCard))).ne'

omit [MeasurableSpace K] [BorelSpace K] in
theorem multHaarConst_ne_zero : multHaarConst K ≠ 0 :=
  ENNReal.inv_ne_zero.mpr (ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self)

omit [MeasurableSpace K] [BorelSpace K] in
theorem multHaarConst_ne_top : multHaarConst K ≠ ∞ :=
  ENNReal.inv_ne_top.mpr one_sub_inv_residueCard_ne_zero

variable (K) in

def multHaar : Measure Kˣ :=
  Measure.comap Units.val
    (multHaarConst K • (haarIntegers K).withDensity fun x => ((modulus x : ℝ≥0∞))⁻¹)

theorem measurable_modulus_inv : Measurable fun x : K => ((modulus x : ℝ≥0∞))⁻¹ :=
  measurable_modulus.coe_nnreal_ennreal.inv

theorem multHaar_apply (s : Set Kˣ) :
    multHaar K s =
      multHaarConst K * ∫⁻ x in Units.val '' s, ((modulus x : ℝ≥0∞))⁻¹ ∂(haarIntegers K) := by
  rw [multHaar, measurableEmbedding_units_val.comap_apply, Measure.smul_apply, withDensity_apply',
    smul_eq_mul]

theorem lintegral_multHaar {g : K → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ u, g u ∂(multHaar K) =
      multHaarConst K * ∫⁻ x in {0}ᶜ, ((modulus x : ℝ≥0∞))⁻¹ * g x ∂(haarIntegers K) := by
  rw [← measurableEmbedding_units_val.lintegral_map, multHaar,
    measurableEmbedding_units_val.map_comap, range_units_val, Measure.restrict_smul,
    lintegral_smul_measure, smul_eq_mul,
    setLIntegral_withDensity_eq_setLIntegral_mul _ measurable_modulus_inv hg
      (measurableSet_singleton 0).compl]
  rfl

theorem integral_multHaar {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : K → E) :
    ∫ u, f u ∂(multHaar K) =
      (multHaarConst K).toReal • ∫ x in {0}ᶜ, ((modulus x : ℝ))⁻¹ • f x ∂(haarIntegers K) := by
  rw [← measurableEmbedding_units_val.integral_map, multHaar,
    measurableEmbedding_units_val.map_comap, range_units_val, Measure.restrict_smul,
    integral_smul_measure,
    setIntegral_withDensity_eq_setIntegral_toReal_smul measurable_modulus_inv
      (ae_restrict_of_forall_mem (measurableSet_singleton 0).compl fun x hx =>
        ENNReal.inv_lt_top.mpr (ENNReal.coe_pos.mpr (modulus_pos hx))) f
      (measurableSet_singleton 0).compl]
  congr 1
  refine setIntegral_congr_fun (measurableSet_singleton 0).compl fun x _ => ?_
  simp [ENNReal.toReal_inv]

instance : (multHaar K).IsMulLeftInvariant := by
  constructor
  intro a
  ext s hs
  have hmeas : Measurable fun u : Kˣ => a * u := by
    rw [← measurableEmbedding_units_val.measurable_comp_iff]
    exact (measurable_const_mul (a : K)).comp measurableEmbedding_units_val.measurable
  rw [Measure.map_apply hmeas hs, multHaar_apply, multHaar_apply]
  congr 1
  have himg : Units.val '' ((fun u => a * u) ⁻¹' s) =
      (fun x : K => (a : K) * x) ⁻¹' (Units.val '' s) := by
    ext x
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨a * u, hu, by simp⟩
    · rintro ⟨v, hv, hvx⟩
      refine ⟨a⁻¹ * v, by simpa using hv, ?_⟩
      simp only [Units.val_mul, hvx]
      rw [← mul_assoc, Units.inv_mul, one_mul]
  rw [himg]
  have hS : MeasurableSet (Units.val '' s) :=
    measurableEmbedding_units_val.measurableSet_image.mpr hs
  have ha0 : (a : K) ≠ 0 := a.ne_zero
  have hm0 : (modulus (a : K) : ℝ≥0∞) ≠ 0 := ENNReal.coe_ne_zero.mpr (modulus_ne_zero ha0)
  have hmt : (modulus (a : K) : ℝ≥0∞) ≠ ∞ := ENNReal.coe_ne_top
  rw [← lintegral_indicator (hS.preimage (measurable_const_mul _)), ← lintegral_indicator hS]
  have hpt : ∀ x, ((fun x : K => (a : K) * x) ⁻¹' (Units.val '' s)).indicator
      (fun x => ((modulus x : ℝ≥0∞))⁻¹) x =
      (Units.val '' s).indicator (fun y => ((modulus y : ℝ≥0∞))⁻¹) ((a : K) * x) *
        (modulus (a : K) : ℝ≥0∞) := by
    intro x
    by_cases hx : (a : K) * x ∈ Units.val '' s
    · rw [Set.indicator_of_mem (show x ∈ (fun x : K => (a : K) * x) ⁻¹' (Units.val '' s) from hx),
        Set.indicator_of_mem hx, modulus_mul, ENNReal.coe_mul,
        ENNReal.mul_inv (Or.inl hm0) (Or.inl hmt), mul_comm, ← mul_assoc,
        ENNReal.mul_inv_cancel hm0 hmt, one_mul]
    · rw [Set.indicator_of_notMem
        (show x ∉ (fun x : K => (a : K) * x) ⁻¹' (Units.val '' s) from hx),
        Set.indicator_of_notMem hx, zero_mul]
  calc ∫⁻ x, ((fun x : K => (a : K) * x) ⁻¹' (Units.val '' s)).indicator
        (fun x => ((modulus x : ℝ≥0∞))⁻¹) x ∂(haarIntegers K)
      = ∫⁻ x, (Units.val '' s).indicator (fun y => ((modulus y : ℝ≥0∞))⁻¹) ((a : K) * x) *
          (modulus (a : K) : ℝ≥0∞) ∂(haarIntegers K) := lintegral_congr hpt
    _ = ((modulus (a : K) : ℝ≥0∞))⁻¹ * ∫⁻ y, (Units.val '' s).indicator
          (fun y => ((modulus y : ℝ≥0∞))⁻¹) y * (modulus (a : K) : ℝ≥0∞) ∂(haarIntegers K) :=
        lintegral_comp_mul_left (haarIntegers K) ha0
          (fun y => (Units.val '' s).indicator (fun y => ((modulus y : ℝ≥0∞))⁻¹) y *
            (modulus (a : K) : ℝ≥0∞))
    _ = ∫⁻ y, (Units.val '' s).indicator (fun y => ((modulus y : ℝ≥0∞))⁻¹) y
          ∂(haarIntegers K) := by
        rw [lintegral_mul_const' _ _ hmt, mul_comm _ (modulus (a : K) : ℝ≥0∞), ← mul_assoc,
          ENNReal.inv_mul_cancel hm0 hmt, one_mul]

instance : IsFiniteMeasureOnCompacts (multHaar K) := by
  constructor
  intro C hC
  rw [multHaar_apply]
  refine ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr multHaarConst_ne_top) ?_
  rcases C.eq_empty_or_nonempty with rfl | hne
  · simp
  have hC' : IsCompact (Units.val '' C) := hC.image Units.continuous_val
  obtain ⟨u, -, hmin⟩ := hC.exists_isMinOn hne
    (continuous_modulus.comp Units.continuous_val).continuousOn
  have hδ : modulus (u : K) ≠ 0 := modulus_ne_zero u.ne_zero
  calc ∫⁻ x in Units.val '' C, ((modulus x : ℝ≥0∞))⁻¹ ∂(haarIntegers K)
      ≤ ∫⁻ x in Units.val '' C, ((modulus (u : K) : ℝ≥0∞))⁻¹ ∂(haarIntegers K) := by
        refine setLIntegral_mono' hC'.isClosed.measurableSet ?_
        rintro _ ⟨v, hv, rfl⟩
        exact ENNReal.inv_le_inv.mpr (ENNReal.coe_le_coe.mpr (hmin hv))
    _ = ((modulus (u : K) : ℝ≥0∞))⁻¹ * haarIntegers K (Units.val '' C) := setLIntegral_const _ _
    _ < ∞ := ENNReal.mul_lt_top (ENNReal.inv_lt_top.mpr (ENNReal.coe_pos.mpr
        (pos_iff_ne_zero.mpr hδ))) hC'.measure_lt_top

instance : IsOpenPosMeasure (multHaar K) := by
  constructor
  intro U hU hne
  rw [multHaar_apply]
  refine mul_ne_zero multHaarConst_ne_zero ?_
  have hU' : IsOpen (Units.val '' U) := isOpenEmbedding_units_val.isOpenMap U hU
  have hpos : 0 < haarIntegers K (Units.val '' U) := hU'.measure_pos _ (hne.image _)
  apply ne_of_gt
  rw [lintegral_pos_iff_support measurable_modulus_inv]
  have : Function.support (fun x : K => ((modulus x : ℝ≥0∞))⁻¹) = Set.univ := by
    ext x
    simp [Function.mem_support]
  rw [this, Measure.restrict_apply_univ]
  exact hpos

instance : (multHaar K).IsHaarMeasure where

theorem multHaar_unitFiltrationUnits_zero :
    multHaar K (unitFiltrationUnits K 0 : Set Kˣ) = 1 := by
  rw [multHaar_apply]
  have himg : Units.val '' (unitFiltrationUnits K 0 : Set Kˣ) =
      (valBall K 0 : Set K) \ valBall K 1 := by
    ext x
    constructor
    · rintro ⟨u, hu, rfl⟩
      rw [SetLike.mem_coe, mem_unitFiltrationUnits_zero_iff] at hu
      exact ⟨mem_valBall_zero_iff.mpr (le_of_eq hu), fun h => (mem_valBall_one_iff.mp h).ne hu⟩
    · rintro ⟨h0, h1⟩
      have hx0 : x ≠ 0 := fun h => h1 (h ▸ zero_mem _)
      refine ⟨Units.mk0 x hx0, ?_, rfl⟩
      rw [SetLike.mem_coe, mem_unitFiltrationUnits_zero_iff, Units.val_mk0]
      have hle : valuation K x ≤ 1 := mem_valBall_zero_iff.mp h0
      have hnlt : ¬ valuation K x < 1 := fun h => h1 (mem_valBall_one_iff.mpr h)
      exact le_antisymm hle (not_lt.mp hnlt)
  rw [himg]
  have hd : ∀ x ∈ (valBall K 0 : Set K) \ valBall K 1, ((modulus x : ℝ≥0∞))⁻¹ = 1 := by
    rintro x ⟨h0, h1⟩
    have hx0 : x ≠ 0 := fun h => h1 (h ▸ zero_mem _)
    have hord : ord x = 0 := by
      have a := (mem_valBall_iff_le_ord hx0).mp h0
      have b := mt (mem_valBall_iff_le_ord hx0).mpr h1
      omega
    rw [modulus_eq_one_iff.mpr ⟨hx0, hord⟩]
    simp
  have hm := (measurableSet_valBall (K := K) 0).diff (measurableSet_valBall 1)
  rw [setLIntegral_congr_fun hm hd, setLIntegral_const, one_mul,
    measure_sdiff (valBall_antitone (by norm_num)) (measurableSet_valBall 1).nullMeasurableSet
      (isCompact_valBall 1).measure_lt_top.ne,
    haarIntegers_valBall, haarIntegers_valBall, neg_zero, zpow_zero, ENNReal.coe_one, zpow_neg_one,
    ENNReal.coe_inv residueCard_nnreal_ne_zero, ENNReal.coe_natCast, multHaarConst,
    ENNReal.inv_mul_cancel one_sub_inv_residueCard_ne_zero
      (ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self)]

end Multiplicative

end GroundTheory.LocalField
