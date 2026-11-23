import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocallyConstantMajorants.GammaSplitting.FunctionalEquationGL2GL1Complex

noncomputable section

open MeasureTheory Matrix Set
open Ad3.K Ad3.K.LC Ad3.K.LC.C

namespace GlobalTheory.CompanionTheory.GodementFE

def nuC : Measure ℂ := volume.withDensity fun z : ℂ => ENNReal.ofReal (‖z‖ ^ 2)⁻¹

theorem range_val : range (Units.val : ℂˣ → ℂ) = {0}ᶜ := by
  ext x
  constructor
  · rintro ⟨u, rfl⟩
    simp
  · intro hx
    exact ⟨Units.mk0 x hx, rfl⟩

theorem val_measEmb : MeasurableEmbedding (Units.val : ℂˣ → ℂ) := by
  refine ⟨fun _ _ h => Units.ext h, comap_measurable _, ?_⟩
  rintro _ ⟨B, hB, rfl⟩
  have : Units.val '' (Units.val ⁻¹' B : Set ℂˣ) = B ∩ {0}ᶜ := by
    rw [image_preimage_eq_inter_range, range_val]
  rw [this]
  exact hB.inter (measurableSet_singleton _).compl

theorem nuC_singleton : nuC {0} = 0 :=
  (withDensity_absolutelyContinuous _ _) (by simp)

theorem map_val_mulC : Measure.map (Units.val : ℂˣ → ℂ) mulC = nuC := by
  have h := val_measEmb.map_comap nuC
  have : nuC.restrict ({0}ᶜ : Set ℂ) = nuC :=
    Measure.restrict_eq_self_of_ae_mem (by
      rw [ae_iff]
      simpa using nuC_singleton)
  rw [range_val, this] at h
  exact h

theorem integral_mulC (F : ℂ → ℂ) :
    ∫ a : ℂˣ, F a ∂mulC = ∫ z : ℂ, (((‖z‖ ^ 2)⁻¹ : ℝ) : ℂ) * F z := by
  have h1 : ∫ a : ℂˣ, F a ∂mulC = ∫ x, F x ∂nuC := by
    rw [← map_val_mulC, val_measEmb.integral_map]
  rw [h1, nuC, integral_withDensity_eq_integral_toReal_smul₀ (by fun_prop) (by simp)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp [ENNReal.toReal_ofReal, Complex.real_smul]

theorem integrable_mulC_iff (F : ℂ → ℂ) :
    Integrable (fun a : ℂˣ => F a) mulC ↔ Integrable (fun z : ℂ => (((‖z‖ ^ 2)⁻¹ : ℝ) : ℂ) * F z) := by
  have h1 : Integrable (fun a : ℂˣ => F a) mulC ↔ Integrable F nuC := by
    rw [← map_val_mulC, val_measEmb.integrable_map_iff]
    rfl
  rw [h1, nuC, integrable_withDensity_iff_integrable_smul₀' (by fun_prop) (by simp)]
  refine integrable_congr (Filter.Eventually.of_forall fun x => ?_)
  simp [ENNReal.toReal_ofReal, Complex.real_smul]

instance : SigmaFinite mulC := by
  refine SigmaFinite.of_map _ val_measEmb.measurable.aemeasurable ?_
  rw [map_val_mulC, nuC]
  exact SigmaFinite.withDensity_ofReal _

def mulL (c : ℂ) : ℂ →L[ℝ] ℂ := ContinuousLinearMap.mul ℝ ℂ c

theorem det_mulL (c : ℂ) : (mulL c).det = Complex.normSq c := by
  have : ((mulL c : ℂ →L[ℝ] ℂ) : ℂ →ₗ[ℝ] ℂ) = Algebra.lmul ℝ ℂ c := by
    ext z
    simp [mulL]
  rw [ContinuousLinearMap.det, this, ← Algebra.norm_apply, Algebra.norm_complex_apply]

theorem nuC_preimage (φ c : ℂ → ℂ) (hφ : Measurable φ)
    (hd : ∀ z, z ≠ 0 → HasFDerivAt φ (mulL (c z)) z)
    (hs : ∀ z, z ≠ 0 → φ z ≠ 0) (hinj : InjOn φ {0}ᶜ) (hsurj : ∀ y, y ≠ 0 → ∃ z, z ≠ 0 ∧ φ z = y)
    (hw : ∀ z, z ≠ 0 → ‖c z‖ ^ 2 * (‖φ z‖ ^ 2)⁻¹ = (‖z‖ ^ 2)⁻¹) {B : Set ℂ} (hB : MeasurableSet B) :
    nuC (φ ⁻¹' B) = nuC B := by
  have hwm : Measurable fun z : ℂ => ENNReal.ofReal (‖z‖ ^ 2)⁻¹ := by fun_prop
  have hcut : ∀ {A : Set ℂ}, MeasurableSet A → nuC A = nuC (A ∩ {0}ᶜ) := by
    intro A hA
    refine (measure_congr ?_)
    have : (A ∩ {0}ᶜ : Set ℂ) =ᵐ[nuC] A := by
      refine inter_ae_eq_left_of_ae_eq_univ ?_
      rw [ae_eq_univ]
      simpa using nuC_singleton
    exact this.symm
  set S : Set ℂ := φ ⁻¹' B ∩ {0}ᶜ with hS
  have hSm : MeasurableSet S := (hφ hB).inter (measurableSet_singleton _).compl
  have himg : φ '' S = B ∩ {0}ᶜ := by
    ext y
    constructor
    · rintro ⟨z, ⟨hz1, hz2⟩, rfl⟩
      exact ⟨hz1, hs z hz2⟩
    · rintro ⟨hy1, hy2⟩
      obtain ⟨z, hz, rfl⟩ := hsurj y hy2
      exact ⟨z, ⟨hy1, hz⟩, rfl⟩
  have key := lintegral_image_eq_lintegral_abs_det_fderiv_mul (volume : Measure ℂ) hSm
    (f := φ) (f' := fun z => mulL (c z)) (fun z hz => (hd z hz.2).hasFDerivWithinAt)
    (hinj.mono inter_subset_right) (fun z : ℂ => ENNReal.ofReal (‖z‖ ^ 2)⁻¹)
  rw [hcut hB, hcut (hφ hB), ← hS, nuC, withDensity_apply _ hSm,
    withDensity_apply _ (hB.inter (measurableSet_singleton _).compl), ← himg, key]
  refine (setLIntegral_congr_fun hSm fun z hz => ?_).symm
  rw [det_mulL, ← ENNReal.ofReal_mul (abs_nonneg _), abs_of_nonneg (Complex.normSq_nonneg _),
    Complex.normSq_eq_norm_sq, hw z hz.2]

theorem nuC_mul (b : ℂˣ) {B : Set ℂ} (hB : MeasurableSet B) :
    nuC ((fun z => (b : ℂ) * z) ⁻¹' B) = nuC B := by
  have hb : (b : ℂ) ≠ 0 := b.ne_zero
  refine nuC_preimage (fun z => (b : ℂ) * z) (fun _ => b) (by fun_prop) ?_ ?_ ?_ ?_ ?_ hB
  · intro z _
    have := (mulL (b : ℂ)).hasFDerivAt (x := z)
    exact this
  · intro z hz
    exact mul_ne_zero hb hz
  · intro x _ y _ h
    exact mul_left_cancel₀ hb h
  · intro y hy
    exact ⟨(b : ℂ)⁻¹ * y, mul_ne_zero (inv_ne_zero hb) hy, by field_simp⟩
  · intro z hz
    have h1 : ‖(b : ℂ)‖ ≠ 0 := norm_ne_zero_iff.2 hb
    have h2 : ‖z‖ ≠ 0 := norm_ne_zero_iff.2 hz
    rw [norm_mul]
    field_simp

theorem nuC_inv {B : Set ℂ} (hB : MeasurableSet B) :
    nuC ((fun z : ℂ => z⁻¹) ⁻¹' B) = nuC B := by
  refine nuC_preimage (fun z => z⁻¹) (fun z => -(z ^ 2)⁻¹) (by fun_prop) ?_ ?_ ?_ ?_ ?_ hB
  · intro z hz
    have h := (hasDerivAt_inv hz).hasFDerivAt.restrictScalars ℝ
    have e : mulL (-(z ^ 2)⁻¹) = ContinuousLinearMap.restrictScalars ℝ
        (ContinuousLinearMap.toSpanSingleton ℂ (-(z ^ 2)⁻¹)) := by
      refine ContinuousLinearMap.ext fun w => ?_
      simp [mulL, mul_comm]
    rw [e]
    exact h
  · intro z hz
    exact inv_ne_zero hz
  · intro x _ y _ h
    exact inv_injective h
  · intro y hy
    exact ⟨y⁻¹, inv_ne_zero hy, inv_inv y⟩
  · intro z hz
    have h2 : ‖z‖ ≠ 0 := norm_ne_zero_iff.2 hz
    simp only [norm_neg, norm_inv, norm_pow]
    field_simp

theorem mulC_preimage {C : Set ℂ} (hC : MeasurableSet C) :
    mulC (Units.val ⁻¹' C) = nuC C := by
  rw [← map_val_mulC, Measure.map_apply val_measEmb.measurable hC]

instance : mulC.IsMulLeftInvariant := by
  refine ⟨fun g => ?_⟩
  ext A hA
  obtain ⟨B, hB, rfl⟩ := hA
  have hm : Measurable fun x : ℂˣ => g * x := measurable_const_mul g
  rw [Measure.map_apply hm (val_measEmb.measurable hB), mulC_preimage hB]
  have : (fun x : ℂˣ => g * x) ⁻¹' (Units.val ⁻¹' B)
      = Units.val ⁻¹' ((fun x : ℂ => (g : ℂ) * x) ⁻¹' B) := by
    ext x
    simp
  rw [this, mulC_preimage ((measurable_const_mul (g : ℂ)) hB), nuC_mul g hB]

theorem mp_inv : MeasurePreserving (fun a : ℂˣ => a⁻¹) mulC mulC := by
  refine ⟨measurable_inv, ?_⟩
  ext A hA
  obtain ⟨B, hB, rfl⟩ := hA
  rw [Measure.map_apply measurable_inv (val_measEmb.measurable hB), mulC_preimage hB]
  have : (fun x : ℂˣ => x⁻¹) ⁻¹' (Units.val ⁻¹' B)
      = Units.val ⁻¹' ((fun x : ℂ => x⁻¹) ⁻¹' B) := by
    ext x
    simp
  have hmi : MeasurableSet ((fun x : ℂ => x⁻¹) ⁻¹' B) := measurable_inv hB
  rw [this, mulC_preimage hmi, nuC_inv hB]

theorem integral_comp_mul (t : ℂ) (ht : t ≠ 0) (g : ℂ → ℂ) :
    ∫ y : ℂ, g (t * y) = (((‖t‖ ^ 2)⁻¹ : ℝ) : ℂ) * ∫ u : ℂ, g u := by
  have hd : LinearMap.det ((mulL t : ℂ →L[ℝ] ℂ) : ℂ →ₗ[ℝ] ℂ) ≠ 0 := by
    have := det_mulL t
    rw [ContinuousLinearMap.det] at this
    rw [this]
    exact (Complex.normSq_pos.2 ht).ne'
  have hmap := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure ℂ) hd
  let e : ℂ ≃ₜ ℂ := Homeomorph.mulLeft₀ t ht
  have he : ⇑e = (((mulL t : ℂ →L[ℝ] ℂ) : ℂ →ₗ[ℝ] ℂ) : ℂ → ℂ) := by
    ext z
    simp [e, mulL]
  have h1 : ∫ y : ℂ, g (t * y) = ∫ u, g u ∂(Measure.map e volume) := by
    rw [e.measurableEmbedding.integral_map]
    rfl
  rw [h1, he, hmap, integral_smul_measure]
  have hdet := det_mulL t
  rw [ContinuousLinearMap.det] at hdet
  rw [hdet, abs_of_nonneg (inv_nonneg.2 (Complex.normSq_nonneg _)), Complex.normSq_eq_norm_sq,
    ENNReal.toReal_ofReal (by positivity), Complex.real_smul]

def dd (z : ℂ) : ℝ := (1 + ‖z‖ ^ 2)⁻¹

theorem dd_pos (z : ℂ) : 0 < dd z := by unfold dd; positivity

theorem continuous_dd : Continuous dd := by
  unfold dd
  refine Continuous.inv₀ (by fun_prop) fun z => by positivity

theorem norm_psiC (x : ℂ) : ‖psiC x‖ = 1 := by
  have : -2 * (Real.pi : ℂ) * Complex.I * (2 * (x.re : ℂ)) = ((-(4 * Real.pi * x.re) : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [psiC, this, Complex.norm_exp_ofReal_mul_I]

theorem continuous_psiC : Continuous psiC := by
  unfold psiC
  have : Continuous fun x : ℂ => (x.re : ℂ) := Complex.continuous_ofReal.comp Complex.continuous_re
  fun_prop

theorem continuous_vec : Continuous fun p : ℂ × ℂ => (![p.1, p.2] : Fin 2 → ℂ) := by
  refine continuous_pi fun i => ?_
  fin_cases i
  · simpa using continuous_fst
  · simpa using continuous_snd

theorem continuous_slice (f : SchwartzMap (Fin 2 → ℂ) ℂ) (x : ℂ) :
    Continuous fun u : ℂ => f ![x, u] :=
  f.continuous.comp (continuous_vec.comp (Continuous.prodMk continuous_const continuous_id))

theorem schw_bound (f : SchwartzMap (Fin 2 → ℂ) ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x u : ℂ, ‖f ![x, u]‖ ≤ C * (dd x * dd u ^ 2) := by
  set K : ℝ := 2 ^ 6 * (Finset.Iic ((6, 0) : ℕ × ℕ)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) f with hK
  have hK0 : 0 ≤ K := by
    have := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (6, 0)) (k := 6) (n := 0) le_rfl le_rfl f 0
    rw [hK]
    exact le_trans (by positivity) this
  refine ⟨K, hK0, fun x u => ?_⟩
  set v : Fin 2 → ℂ := ![x, u] with hv
  have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (6, 0)) (k := 6) (n := 0) le_rfl le_rfl f v
  rw [norm_iteratedFDeriv_zero] at h
  have hx : ‖x‖ ≤ ‖v‖ := by simpa [hv] using norm_le_pi_norm v 0
  have hu : ‖u‖ ≤ ‖v‖ := by simpa [hv] using norm_le_pi_norm v 1
  have hr : 0 ≤ ‖v‖ := norm_nonneg _
  have hA : 1 + ‖x‖ ^ 2 ≤ (1 + ‖v‖) ^ 2 := by nlinarith [norm_nonneg x]
  have hB : 1 + ‖u‖ ^ 2 ≤ (1 + ‖v‖) ^ 2 := by nlinarith [norm_nonneg u]
  have hAB : (1 + ‖x‖ ^ 2) * (1 + ‖u‖ ^ 2) ^ 2 ≤ (1 + ‖v‖) ^ 6 := by
    have h2 : (1 + ‖u‖ ^ 2) ^ 2 ≤ ((1 + ‖v‖) ^ 2) ^ 2 := pow_le_pow_left₀ (by positivity) hB 2
    calc (1 + ‖x‖ ^ 2) * (1 + ‖u‖ ^ 2) ^ 2 ≤ (1 + ‖v‖) ^ 2 * ((1 + ‖v‖) ^ 2) ^ 2 :=
          mul_le_mul hA h2 (by positivity) (by positivity)
      _ = (1 + ‖v‖) ^ 6 := by ring
  have h3 : (1 + ‖x‖ ^ 2) * (1 + ‖u‖ ^ 2) ^ 2 * ‖f v‖ ≤ K :=
    le_trans (mul_le_mul_of_nonneg_right hAB (norm_nonneg _)) h
  have hpos : 0 < (1 + ‖x‖ ^ 2) * (1 + ‖u‖ ^ 2) ^ 2 := by positivity
  have e : K * (dd x * dd u ^ 2) = K / ((1 + ‖x‖ ^ 2) * (1 + ‖u‖ ^ 2) ^ 2) := by
    simp only [dd]
    field_simp
  rw [e, le_div_iff₀ hpos, mul_comm]
  exact h3

theorem wt_vol (σ : ℝ) (h0 : 0 < σ) (h1 : σ < 1) :
    Integrable fun z : ℂ => ‖z‖ ^ (2 * σ - 2) * dd z := by
  set G : ℝ → ℝ := fun r => r ^ (2 * σ - 2) * (1 + r ^ 2)⁻¹ with hG
  have hm : Measurable fun y : ℝ => y ^ (Module.finrank ℝ ℂ - 1) • G y := by
    simp only [hG]
    fun_prop
  have hfin : IntegrableOn (fun y : ℝ => y ^ (Module.finrank ℝ ℂ - 1) • G y) (Ioi 0) volume := by
    have hsplit : Ioi (0 : ℝ) = Ioc 0 1 ∪ Ioi 1 := (Ioc_union_Ioi_eq_Ioi zero_le_one).symm
    rw [hsplit]
    refine IntegrableOn.union ?_ ?_
    · have hb : IntegrableOn (fun y : ℝ => y ^ (2 * σ - 1)) (Ioc 0 1) volume := by
        have := intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1) (r := 2 * σ - 1) (by linarith)
        exact (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1 this
      refine Integrable.mono' hb hm.aestronglyMeasurable ?_
      refine (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun y hy => ?_)
      have hy0 : 0 < y := hy.1
      simp only [hG, Complex.finrank_real_complex, smul_eq_mul]
      rw [Real.norm_of_nonneg (by positivity)]
      have e : y ^ (2 * σ - 1) = y ^ (2 - 1) * y ^ (2 * σ - 2) := by
        rw [show (2 - 1 : ℕ) = 1 from rfl, pow_one]
        nth_rewrite 2 [← Real.rpow_one y]
        rw [← Real.rpow_add hy0]
        congr 1
        ring
      rw [e]
      have hinv : (1 + y ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg y])
      have hp : 0 ≤ y ^ (2 - 1) * y ^ (2 * σ - 2) := by positivity
      calc y ^ (2 - 1) * (y ^ (2 * σ - 2) * (1 + y ^ 2)⁻¹)
          = (y ^ (2 - 1) * y ^ (2 * σ - 2)) * (1 + y ^ 2)⁻¹ := by ring
        _ ≤ (y ^ (2 - 1) * y ^ (2 * σ - 2)) * 1 := mul_le_mul_of_nonneg_left hinv hp
        _ = _ := mul_one _
    · have hb : IntegrableOn (fun y : ℝ => y ^ (2 * σ - 3)) (Ioi 1) volume :=
        integrableOn_Ioi_rpow_of_lt (by linarith) one_pos
      refine Integrable.mono' hb hm.aestronglyMeasurable ?_
      refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun y hy => ?_)
      have hy0 : 0 < y := lt_trans one_pos hy
      simp only [hG, Complex.finrank_real_complex, smul_eq_mul]
      rw [Real.norm_of_nonneg (by positivity)]
      have e : y ^ (2 * σ - 3) = y ^ (2 - 1) * y ^ (2 * σ - 2) * (y ^ 2)⁻¹ := by
        rw [show (2 - 1 : ℕ) = 1 from rfl, pow_one, ← Real.rpow_natCast y 2, ← Real.rpow_neg hy0.le]
        nth_rewrite 2 [← Real.rpow_one y]
        rw [← Real.rpow_add hy0, ← Real.rpow_add hy0]
        congr 1
        push_cast
        ring
      rw [e]
      have hinv : (1 + y ^ 2)⁻¹ ≤ (y ^ 2)⁻¹ :=
        inv_anti₀ (by positivity) (by linarith)
      have hp : 0 ≤ y ^ (2 - 1) * y ^ (2 * σ - 2) := by positivity
      calc y ^ (2 - 1) * (y ^ (2 * σ - 2) * (1 + y ^ 2)⁻¹)
          = (y ^ (2 - 1) * y ^ (2 * σ - 2)) * (1 + y ^ 2)⁻¹ := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hinv hp
  have := (integrable_fun_norm_addHaar (volume : Measure ℂ) (f := G)).2 hfin
  exact this

theorem dd_sq_int : Integrable fun u : ℂ => dd u ^ 2 := by
  have h := wt_vol (1 / 2) (by norm_num) (by norm_num)
  refine h.mono' (by have := continuous_dd; fun_prop) ?_
  filter_upwards [compl_mem_ae_iff.2 (measure_singleton (0 : ℂ))] with z hz
  have hz0 : ‖z‖ ≠ 0 := norm_ne_zero_iff.2 hz
  have hzp : 0 < ‖z‖ := norm_pos_iff.2 hz
  rw [Real.norm_of_nonneg (by have := dd_pos z; positivity), pow_two]
  refine mul_le_mul_of_nonneg_right ?_ (dd_pos z).le
  have e : (2 * (1 / 2 : ℝ) - 2) = -1 := by norm_num
  rw [e, Real.rpow_neg_one]
  unfold dd
  exact inv_anti₀ hzp (by nlinarith [sq_nonneg (‖z‖ - 1), norm_nonneg z])

theorem slice_int (f : SchwartzMap (Fin 2 → ℂ) ℂ) (x : ℂ) : Integrable fun u : ℂ => f ![x, u] := by
  obtain ⟨C, hC, hb⟩ := schw_bound f
  refine (dd_sq_int.const_mul (C * dd x)).mono' (continuous_slice f x).aestronglyMeasurable
    (Filter.Eventually.of_forall fun u => ?_)
  calc ‖f ![x, u]‖ ≤ C * (dd x * dd u ^ 2) := hb x u
    _ = _ := by ring

theorem slice_psi_int (f : SchwartzMap (Fin 2 → ℂ) ℂ) (x ξ : ℂ) :
    Integrable fun u : ℂ => f ![x, u] * psiC (-(u * ξ)) := by
  refine (slice_int f x).norm.mono' ?_ (Filter.Eventually.of_forall fun u => ?_)
  · exact ((continuous_slice f x).mul (continuous_psiC.comp (by fun_prop))).aestronglyMeasurable
  · rw [norm_mul, norm_psiC, mul_one]

def sF (f : (Fin 2 → ℂ) → ℂ) (x ξ : ℂ) : ℂ := ∫ u : ℂ, f ![x, u] * psiC (-(u * ξ))

theorem sF_bound0 (f : SchwartzMap (Fin 2 → ℂ) ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ξ : ℂ, ‖sF f x ξ‖ ≤ C * dd x := by
  obtain ⟨C, hC, hb⟩ := schw_bound f
  have hJ : 0 ≤ ∫ u : ℂ, dd u ^ 2 := integral_nonneg fun u => by positivity
  refine ⟨C * ∫ u : ℂ, dd u ^ 2, by positivity, fun x ξ => ?_⟩
  have h1 : ‖sF f x ξ‖ ≤ ∫ u : ℂ, C * dd x * dd u ^ 2 := by
    refine norm_integral_le_of_norm_le (dd_sq_int.const_mul _) (Filter.Eventually.of_forall fun u => ?_)
    rw [norm_mul, norm_psiC, mul_one]
    calc ‖f ![x, u]‖ ≤ C * (dd x * dd u ^ 2) := hb x u
      _ = _ := by ring
  rw [integral_const_mul] at h1
  calc _ ≤ _ := h1
    _ = _ := by ring

theorem psi_line (e ξ u : ℂ) :
    HasLineDerivAt ℝ (fun u : ℂ => psiC (-(u * ξ)))
      (4 * Real.pi * Complex.I * (e * ξ).re * psiC (-(u * ξ))) u e := by
  set c : ℂ := 4 * Real.pi * Complex.I * (e * ξ).re with hc
  have h1 : HasDerivAt (fun z : ℂ => Complex.exp (z * c)) (Complex.exp (0 * c) * c) 0 := by
    have : HasDerivAt (fun z : ℂ => z * c) c 0 := by
      simpa using (hasDerivAt_id (0 : ℂ)).mul_const c
    exact this.cexp
  have h2 : HasDerivAt (fun t : ℝ => Complex.exp ((t : ℂ) * c)) c 0 := by
    have := h1.comp_ofReal
    simpa using this
  have h3 := h2.const_mul (psiC (-(u * ξ)))
  unfold HasLineDerivAt
  have e1 : (fun t : ℝ => psiC (-((u + t • e) * ξ))) =
      fun t : ℝ => psiC (-(u * ξ)) * Complex.exp ((t : ℂ) * c) := by
    funext t
    simp only [psiC, ← Complex.exp_add]
    congr 1
    simp only [hc, Complex.real_smul, add_mul, neg_add, Complex.add_re, Complex.neg_re, mul_assoc,
      Complex.re_ofReal_mul]
    push_cast
    ring
  rw [e1, mul_comm c]
  exact h3

theorem slice_line (f : SchwartzMap (Fin 2 → ℂ) ℂ) (e x u : ℂ) :
    HasLineDerivAt ℝ (fun u : ℂ => f ![x, u]) ((LineDeriv.lineDerivOp (![0, e] : Fin 2 → ℂ) f) ![x, u]) u e := by
  have h := (f.differentiableAt (x := ![x, u])).hasFDerivAt.hasLineDerivAt (![0, e] : Fin 2 → ℂ)
  rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]
  unfold HasLineDerivAt at h ⊢
  have e1 : (fun t : ℝ => f ![x, u + t • e]) = fun t : ℝ => f (![x, u] + t • ![0, e]) := by
    funext t
    congr 1
    ext i
    fin_cases i <;> simp
  rw [e1]
  exact h

theorem sF_deriv (f : SchwartzMap (Fin 2 → ℂ) ℂ) (e x ξ : ℂ) :
    sF (LineDeriv.lineDerivOp (![0, e] : Fin 2 → ℂ) f) x ξ =
      -(4 * Real.pi * Complex.I * (e * ξ).re) * sF f x ξ := by
  set c : ℂ := 4 * Real.pi * Complex.I * (e * ξ).re with hc
  set D := LineDeriv.lineDerivOp (![0, e] : Fin 2 → ℂ) f with hD
  have h := integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable (μ := (volume : Measure ℂ))
    (B := ContinuousLinearMap.mul ℝ ℂ) (v := e) (f := fun u : ℂ => f ![x, u]) (f' := fun u : ℂ => D ![x, u])
    (g := fun u : ℂ => psiC (-(u * ξ))) (g' := fun u : ℂ => c * psiC (-(u * ξ)))
    (by simpa using slice_psi_int D x ξ)
    (by
      have := (slice_psi_int f x ξ).const_mul c
      refine this.congr (Filter.Eventually.of_forall fun u => ?_)
      simp only [ContinuousLinearMap.mul_apply']
      ring)
    (by simpa using slice_psi_int f x ξ)
    (fun u _ => slice_line f e x u) (fun u _ => psi_line e ξ u)
  simp only [ContinuousLinearMap.mul_apply'] at h
  have h2 : ∫ u : ℂ, f ![x, u] * (c * psiC (-(u * ξ))) = c * sF f x ξ := by
    rw [sF, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp only
    ring
  rw [h2] at h
  have h3 : sF D x ξ = ∫ u : ℂ, D ![x, u] * psiC (-(u * ξ)) := rfl
  rw [h3]
  linear_combination h

theorem sF_decay (f : SchwartzMap (Fin 2 → ℂ) ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ξ : ℂ, ‖sF f x ξ‖ ≤ C * (dd x * dd ξ) := by
  set D1 := LineDeriv.lineDerivOp (![0, 1] : Fin 2 → ℂ) (LineDeriv.lineDerivOp (![0, 1] : Fin 2 → ℂ) f) with hD1
  set D2 := LineDeriv.lineDerivOp (![0, Complex.I] : Fin 2 → ℂ) (LineDeriv.lineDerivOp (![0, Complex.I] : Fin 2 → ℂ) f) with hD2
  obtain ⟨C0, hC0, b0⟩ := sF_bound0 f
  obtain ⟨C1, hC1, b1⟩ := sF_bound0 D1
  obtain ⟨C2, hC2, b2⟩ := sF_bound0 D2
  refine ⟨C0 + C1 + C2, by positivity, fun x ξ => ?_⟩
  have e1 : sF D1 x ξ = (-(4 * Real.pi * Complex.I * ξ.re)) ^ 2 * sF f x ξ := by
    rw [hD1, sF_deriv, sF_deriv]
    simp only [one_mul]
    ring
  have e2 : sF D2 x ξ = (-(4 * Real.pi * Complex.I * ξ.im)) ^ 2 * sF f x ξ := by
    rw [hD2, sF_deriv, sF_deriv]
    simp only [Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_sub]
    push_cast
    ring
  have n1 : (4 * Real.pi) ^ 2 * ξ.re ^ 2 * ‖sF f x ξ‖ ≤ C1 * dd x := by
    have := b1 x ξ
    rw [e1, norm_mul, norm_pow, norm_neg] at this
    have e : ‖4 * (Real.pi : ℂ) * Complex.I * (ξ.re : ℂ)‖ = 4 * Real.pi * |ξ.re| := by
      simp [abs_of_pos Real.pi_pos]
    rw [e, mul_pow, sq_abs] at this
    exact this
  have n2 : (4 * Real.pi) ^ 2 * ξ.im ^ 2 * ‖sF f x ξ‖ ≤ C2 * dd x := by
    have := b2 x ξ
    rw [e2, norm_mul, norm_pow, norm_neg] at this
    have e : ‖4 * (Real.pi : ℂ) * Complex.I * (ξ.im : ℂ)‖ = 4 * Real.pi * |ξ.im| := by
      simp [abs_of_pos Real.pi_pos]
    rw [e, mul_pow, sq_abs] at this
    exact this
  have n0 := b0 x ξ
  have hpi : (1 : ℝ) ≤ (4 * Real.pi) ^ 2 := by nlinarith [Real.pi_gt_three]
  have hsq : ‖ξ‖ ^ 2 = ξ.re ^ 2 + ξ.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  have hS : 0 ≤ ‖sF f x ξ‖ := norm_nonneg _
  have hmain : (1 + ‖ξ‖ ^ 2) * ‖sF f x ξ‖ ≤ (C0 + C1 + C2) * dd x := by
    rw [hsq]
    have a1 : ξ.re ^ 2 * ‖sF f x ξ‖ ≤ (4 * Real.pi) ^ 2 * ξ.re ^ 2 * ‖sF f x ξ‖ := by
      have : 0 ≤ ξ.re ^ 2 * ‖sF f x ξ‖ := by positivity
      nlinarith
    have a2 : ξ.im ^ 2 * ‖sF f x ξ‖ ≤ (4 * Real.pi) ^ 2 * ξ.im ^ 2 * ‖sF f x ξ‖ := by
      have : 0 ≤ ξ.im ^ 2 * ‖sF f x ξ‖ := by positivity
      nlinarith
    nlinarith
  have hpos : 0 < 1 + ‖ξ‖ ^ 2 := by positivity
  have e : (C0 + C1 + C2) * (dd x * dd ξ) = (C0 + C1 + C2) * dd x / (1 + ‖ξ‖ ^ 2) := by
    simp only [dd]
    field_simp
  rw [e, le_div_iff₀ hpos, mul_comm]
  exact hmain

theorem measurable_sF (f : SchwartzMap (Fin 2 → ℂ) ℂ) :
    Measurable fun p : ℂ × ℂ => sF f p.1 p.2 := by
  have hc : Continuous fun q : (ℂ × ℂ) × ℂ => f ![q.1.1, q.2] * psiC (-(q.2 * q.1.2)) := by
    have h1 : Continuous fun q : (ℂ × ℂ) × ℂ => psiC (-(q.2 * q.1.2)) := by
      have : Continuous fun q : (ℂ × ℂ) × ℂ => -(q.2 * q.1.2) := by fun_prop
      exact continuous_psiC.comp this
    have h2 : Continuous fun q : (ℂ × ℂ) × ℂ => (q.1.1, q.2) := by fun_prop
    exact (f.continuous.comp (continuous_vec.comp h2)).mul h1
  exact (hc.stronglyMeasurable.integral_prod_right' (ν := (volume : Measure ℂ))).measurable

end GlobalTheory.CompanionTheory.GodementFE
