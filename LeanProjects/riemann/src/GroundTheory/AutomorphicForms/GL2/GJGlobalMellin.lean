import Mathlib
import GroundTheory.AutomorphicForms.GL2.GJGlobalHaar

open MeasureTheory NumberField Set ComplexConjugate
open scoped NumberField.AdeleRing ENNReal NNReal

namespace GroundTheory.Automorphic

noncomputable section

namespace GJGlobal

open Reduction RightCosetSpace GroundTheory.Global

set_option linter.unusedSectionVars false

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

def ratElt (γ : GL (Fin n) K) : normOneGL K n :=
  ⟨AdelicGLn.diagonal K n γ, rationalGL_le_normOneGL ⟨γ, rfl⟩⟩

@[simp] theorem coe_ratElt (γ : GL (Fin n) K) :
    ((ratElt γ : normOneGL K n) : AdelicGLn.AdelicGL K n) = AdelicGLn.diagonal K n γ :=
  rfl

theorem ratElt_mem (γ : GL (Fin n) K) : ratElt γ ∈ rationalGLOne K n :=
  Subgroup.mem_subgroupOf.2 ⟨γ, rfl⟩

def ratEquiv : GL (Fin n) K ≃ rationalGLOne K n :=
  Equiv.ofBijective (fun γ => ⟨ratElt γ, ratElt_mem γ⟩)
    ⟨fun γ γ' h => AdelicGLn.diagonal_injective K n
      (congrArg (fun x : rationalGLOne K n => ((x : normOneGL K n) : AdelicGLn.AdelicGL K n)) h),
     fun x => by
       obtain ⟨γ, hγ⟩ := Subgroup.mem_subgroupOf.1 x.2
       exact ⟨γ, Subtype.ext (Subtype.ext hγ)⟩⟩

@[simp] theorem coe_ratEquiv (γ : GL (Fin n) K) :
    ((ratEquiv γ : rationalGLOne K n) : normOneGL K n) = ratElt γ :=
  rfl

variable (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure]

theorem lintegral_eq_setLIntegral_tsum {h : normOneGL K n → ℝ≥0∞} (hh : Measurable h) :
    ∫⁻ y, h y ∂μ = ∫⁻ y in fundamentalDomain (rationalGLOne K n),
      ∑' γ : GL (Fin n) K, h (ratElt γ * y) ∂μ := by
  rw [lintegral_eq_lintegral_automorphize (Γ := rationalGLOne K n) μ hh.aemeasurable,
    lintegral_quotientMeasure]
  refine lintegral_congr fun y => ?_
  change ∑' γ : rationalGLOne K n, h (γ • y) = _
  rw [← (ratEquiv (K := K) (n := n)).tsum_eq]
  rfl

theorem integral_eq_setIntegral_tsum {h : normOneGL K n → ℂ} (hh : Integrable h μ) :
    ∫ y, h y ∂μ = ∫ y in fundamentalDomain (rationalGLOne K n),
      ∑' γ : GL (Fin n) K, h (ratElt γ * y) ∂μ := by
  rw [integral_eq_integral_automorphize (Γ := rationalGLOne K n) μ hh, integral_quotientMeasure]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  change ∑' γ : rationalGLOne K n, h (γ • y) = _
  rw [← (ratEquiv (K := K) (n := n)).tsum_eq]
  rfl

theorem measure_fundamentalDomain_rationalGLOne_lt_top :
    μ (fundamentalDomain (rationalGLOne K n)) < ⊤ := by
  have := isFiniteMeasure_quotientMeasure (K := K) (n := n) μ
  exact (measure_fundamentalDomain_pos_lt_top (rationalGLOne K n) μ).2

theorem lintegral_posRealMeasure (f : ℝ → ℝ≥0∞) :
    ∫⁻ t, f t ∂posRealMeasure = ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal t⁻¹ * f t := by
  rw [posRealMeasure]
  have h := lintegral_subtype_comap (μ := volume.withDensity fun t : ℝ ↦ ENNReal.ofReal t⁻¹)
    (s := Ioi (0 : ℝ)) measurableSet_Ioi f
  refine h.trans ?_
  have hm : Measurable fun t : ℝ ↦ ENNReal.ofReal t⁻¹ := ENNReal.measurable_ofReal.comp measurable_inv
  rw [setLIntegral_withDensity_eq_setLIntegral_mul_non_measurable _ hm f measurableSet_Ioi
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  rfl

section Pairing

variable {φ₁ φ₂ Ξ : AdelicGLn.AdelicGL K n → ℂ}

theorem lintegral_enorm_translate_eq (hφ₁ : Continuous φ₁) (hφ₁l : AutomorphicForm.IsLeftInvariant φ₁)
    (hΞ : Continuous Ξ) (s : {r : ℝ // 0 < r}) (x : AdelicGLn.AdelicGL K n) :
    ∫⁻ y, ‖Ξ (centralSection K n s * x * (y : AdelicGLn.AdelicGL K n))‖ₑ *
        ‖φ₁ (y : AdelicGLn.AdelicGL K n)‖ₑ ∂μ =
      ∫⁻ y in fundamentalDomain (rationalGLOne K n), ‖φ₁ (y : AdelicGLn.AdelicGL K n)‖ₑ *
        ∑' γ : GL (Fin n) K, ‖Ξ (centralSection K n s * x * AdelicGLn.diagonal K n γ *
          (y : AdelicGLn.AdelicGL K n))‖ₑ ∂μ := by
  have hm : Measurable fun y : normOneGL K n =>
      ‖Ξ (centralSection K n s * x * (y : AdelicGLn.AdelicGL K n))‖ₑ *
        ‖φ₁ (y : AdelicGLn.AdelicGL K n)‖ₑ :=
    (hΞ.comp (continuous_const.mul continuous_subtype_val)).enorm.measurable.mul
      (hφ₁.comp continuous_subtype_val).enorm.measurable
  rw [lintegral_eq_setLIntegral_tsum μ hm]
  refine lintegral_congr fun y => ?_
  rw [← ENNReal.tsum_mul_left]
  refine tsum_congr fun γ => ?_
  simp only [Subgroup.coe_mul, coe_ratElt]
  rw [hφ₁l, mul_comm]
  simp only [mul_assoc]

theorem enorm_mul_lintegral_le (hφ₁ : Continuous φ₁) (hφ₁l : AutomorphicForm.IsLeftInvariant φ₁)
    (hΞ : Continuous Ξ) {B : ℝ → ℝ}
    (hB : ∀ (t : {r : ℝ // 0 < r}) (x y : AdelicGLn.AdelicGL K n), x ∈ normOneGL K n →
      y ∈ normOneGL K n →
      Summable (fun γ : GL (Fin n) K =>
        ‖Ξ (centralSection K n t * x⁻¹ * AdelicGLn.diagonal K n γ * y)‖) ∧
      ‖φ₂ x‖ * ‖φ₁ y‖ * ∑' γ : GL (Fin n) K,
        ‖Ξ (centralSection K n t * x⁻¹ * AdelicGLn.diagonal K n γ * y)‖ ≤ B t)
    (s : {r : ℝ // 0 < r}) (x : normOneGL K n) :
    ‖φ₂ (x : AdelicGLn.AdelicGL K n)‖ₑ *
        ∫⁻ y, ‖Ξ (centralSection K n s * (x : AdelicGLn.AdelicGL K n)⁻¹ *
          (y : AdelicGLn.AdelicGL K n))‖ₑ * ‖φ₁ (y : AdelicGLn.AdelicGL K n)‖ₑ ∂μ ≤
      ENNReal.ofReal (B s) * μ (fundamentalDomain (rationalGLOne K n)) := by
  rw [lintegral_enorm_translate_eq μ hφ₁ hφ₁l hΞ, ← lintegral_const_mul' _ _ enorm_ne_top,
    ← setLIntegral_const]
  refine lintegral_mono fun y => ?_
  obtain ⟨hs, hle⟩ := hB s x y x.2 y.2
  have e1 : ∑' γ : GL (Fin n) K, ‖Ξ (centralSection K n s * (x : AdelicGLn.AdelicGL K n)⁻¹ *
        AdelicGLn.diagonal K n γ * (y : AdelicGLn.AdelicGL K n))‖ₑ =
      ENNReal.ofReal (∑' γ : GL (Fin n) K, ‖Ξ (centralSection K n s *
        (x : AdelicGLn.AdelicGL K n)⁻¹ * AdelicGLn.diagonal K n γ * (y : AdelicGLn.AdelicGL K n))‖) := by
    rw [ENNReal.ofReal_tsum_of_nonneg (fun _ => norm_nonneg _) hs]
    simp only [ofReal_norm]
  rw [e1, ← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul (norm_nonneg _),
    ← ENNReal.ofReal_mul (norm_nonneg _)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [← mul_assoc]
  exact hle

theorem lintegral_lintegral_enorm_le (hφ₁ : Continuous φ₁) (hφ₁l : AutomorphicForm.IsLeftInvariant φ₁)
    (hΞ : Continuous Ξ) {B : ℝ → ℝ}
    (hB : ∀ (t : {r : ℝ // 0 < r}) (x y : AdelicGLn.AdelicGL K n), x ∈ normOneGL K n →
      y ∈ normOneGL K n →
      Summable (fun γ : GL (Fin n) K =>
        ‖Ξ (centralSection K n t * x⁻¹ * AdelicGLn.diagonal K n γ * y)‖) ∧
      ‖φ₂ x‖ * ‖φ₁ y‖ * ∑' γ : GL (Fin n) K,
        ‖Ξ (centralSection K n t * x⁻¹ * AdelicGLn.diagonal K n γ * y)‖ ≤ B t)
    (s : {r : ℝ // 0 < r}) :
    ∫⁻ x in fundamentalDomain (rationalGLOne K n), ∫⁻ y,
        ‖Ξ (centralSection K n s * (y : AdelicGLn.AdelicGL K n))‖ₑ *
          ‖φ₁ ((x : AdelicGLn.AdelicGL K n) * (y : AdelicGLn.AdelicGL K n))‖ₑ *
          ‖φ₂ (x : AdelicGLn.AdelicGL K n)‖ₑ ∂μ ∂μ ≤
      ENNReal.ofReal (B s) * μ (fundamentalDomain (rationalGLOne K n)) *
        μ (fundamentalDomain (rationalGLOne K n)) := by
  rw [← setLIntegral_const]
  refine lintegral_mono fun x => ?_
  have h1 : ∫⁻ y, ‖Ξ (centralSection K n s * (y : AdelicGLn.AdelicGL K n))‖ₑ *
        ‖φ₁ ((x : AdelicGLn.AdelicGL K n) * (y : AdelicGLn.AdelicGL K n))‖ₑ *
        ‖φ₂ (x : AdelicGLn.AdelicGL K n)‖ₑ ∂μ =
      ‖φ₂ (x : AdelicGLn.AdelicGL K n)‖ₑ *
        ∫⁻ y, ‖Ξ (centralSection K n s * (x : AdelicGLn.AdelicGL K n)⁻¹ *
          (y : AdelicGLn.AdelicGL K n))‖ₑ * ‖φ₁ (y : AdelicGLn.AdelicGL K n)‖ₑ ∂μ := by
    calc ∫⁻ y, ‖Ξ (centralSection K n s * (y : AdelicGLn.AdelicGL K n))‖ₑ *
          ‖φ₁ ((x : AdelicGLn.AdelicGL K n) * (y : AdelicGLn.AdelicGL K n))‖ₑ *
          ‖φ₂ (x : AdelicGLn.AdelicGL K n)‖ₑ ∂μ
        = ∫⁻ y, (fun y : normOneGL K n => ‖φ₂ (x : AdelicGLn.AdelicGL K n)‖ₑ *
            (‖Ξ (centralSection K n s * (x : AdelicGLn.AdelicGL K n)⁻¹ *
              (y : AdelicGLn.AdelicGL K n))‖ₑ * ‖φ₁ (y : AdelicGLn.AdelicGL K n)‖ₑ)) (x * y) ∂μ := by
          refine lintegral_congr fun y => ?_
          simp only [Subgroup.coe_mul, mul_assoc, inv_mul_cancel_left]
          ring
      _ = ∫⁻ y, ‖φ₂ (x : AdelicGLn.AdelicGL K n)‖ₑ *
            (‖Ξ (centralSection K n s * (x : AdelicGLn.AdelicGL K n)⁻¹ *
              (y : AdelicGLn.AdelicGL K n))‖ₑ * ‖φ₁ (y : AdelicGLn.AdelicGL K n)‖ₑ) ∂μ :=
          lintegral_mul_left_eq_self (μ := μ) (fun y : normOneGL K n =>
            ‖φ₂ (x : AdelicGLn.AdelicGL K n)‖ₑ * (‖Ξ (centralSection K n s *
              (x : AdelicGLn.AdelicGL K n)⁻¹ * (y : AdelicGLn.AdelicGL K n))‖ₑ *
                ‖φ₁ (y : AdelicGLn.AdelicGL K n)‖ₑ)) x
      _ = _ := lintegral_const_mul' _ _ enorm_ne_top
  rw [h1]
  exact enorm_mul_lintegral_le μ hφ₁ hφ₁l hΞ hB s x

end Pairing

section Identity

variable {φ₁ φ₂ Ξ : AdelicGLn.AdelicGL K n → ℂ}

theorem integral_mul_matrixCoeff_eq_thetaPairing (hφ₁ : Continuous φ₁) (hφ₂ : Continuous φ₂)
    (hφ₁l : AutomorphicForm.IsLeftInvariant φ₁) (hΞ : Continuous Ξ) {B : ℝ → ℝ}
    (hB : ∀ (t : {r : ℝ // 0 < r}) (x y : AdelicGLn.AdelicGL K n), x ∈ normOneGL K n →
      y ∈ normOneGL K n →
      Summable (fun γ : GL (Fin n) K =>
        ‖Ξ (centralSection K n t * x⁻¹ * AdelicGLn.diagonal K n γ * y)‖) ∧
      ‖φ₂ x‖ * ‖φ₁ y‖ * ∑' γ : GL (Fin n) K,
        ‖Ξ (centralSection K n t * x⁻¹ * AdelicGLn.diagonal K n γ * y)‖ ≤ B t)
    (s : {r : ℝ // 0 < r}) :
    ∫ y, Ξ (centralSection K n s * (y : AdelicGLn.AdelicGL K n)) *
        matrixCoeff μ φ₁ φ₂ (y : AdelicGLn.AdelicGL K n) ∂μ = thetaPairing μ φ₁ φ₂ Ξ s := by
  set F := fundamentalDomain (rationalGLOne K n) with hF
  have hFfin := measure_fundamentalDomain_rationalGLOne_lt_top μ
  set f : normOneGL K n → normOneGL K n → ℂ := fun y x =>
    Ξ (centralSection K n s * (y : AdelicGLn.AdelicGL K n)) *
      (φ₁ ((x : AdelicGLn.AdelicGL K n) * (y : AdelicGLn.AdelicGL K n)) *
        conj (φ₂ (x : AdelicGLn.AdelicGL K n))) with hfdef
  have hcont : Continuous (Function.uncurry f) :=
    (hΞ.comp (continuous_const.mul (continuous_subtype_val.comp continuous_fst))).mul
      ((hφ₁.comp ((continuous_subtype_val.comp continuous_snd).mul
        (continuous_subtype_val.comp continuous_fst))).mul
        (Complex.continuous_conj.comp (hφ₂.comp (continuous_subtype_val.comp continuous_snd))))
  have hint : Integrable (Function.uncurry f) (μ.prod (μ.restrict F)) := by
    refine ⟨hcont.aestronglyMeasurable, ?_⟩
    rw [HasFiniteIntegral, lintegral_prod _ hcont.enorm.measurable.aemeasurable]
    rw [lintegral_lintegral_swap (hcont.enorm.measurable.aemeasurable)]
    have h1 : ∀ x y : normOneGL K n, ‖Function.uncurry f (y, x)‖ₑ =
        ‖Ξ (centralSection K n s * (y : AdelicGLn.AdelicGL K n))‖ₑ *
          ‖φ₁ ((x : AdelicGLn.AdelicGL K n) * (y : AdelicGLn.AdelicGL K n))‖ₑ *
          ‖φ₂ (x : AdelicGLn.AdelicGL K n)‖ₑ := by
      intro x y
      simp only [Function.uncurry_apply_pair, hfdef, enorm_mul, RCLike.enorm_conj, mul_assoc]
    simp_rw [h1]
    refine lt_of_le_of_lt (lintegral_lintegral_enorm_le μ hφ₁ hφ₁l hΞ hB s) ?_
    exact ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hFfin) hFfin
  have hstep : ∀ x : normOneGL K n, ∫ y, f y x ∂μ =
      ∫ y in F, conj (φ₂ (x : AdelicGLn.AdelicGL K n)) * φ₁ (y : AdelicGLn.AdelicGL K n) *
        ∑' γ : GL (Fin n) K, Ξ (centralSection K n s * (x : AdelicGLn.AdelicGL K n)⁻¹ *
          AdelicGLn.diagonal K n γ * (y : AdelicGLn.AdelicGL K n)) ∂μ := by
    intro x
    set h : normOneGL K n → ℂ := fun y => Ξ (centralSection K n s *
      (x : AdelicGLn.AdelicGL K n)⁻¹ * (y : AdelicGLn.AdelicGL K n)) *
        φ₁ (y : AdelicGLn.AdelicGL K n) with hhdef
    have e1 : ∫ y, f y x ∂μ = conj (φ₂ (x : AdelicGLn.AdelicGL K n)) * ∫ y, h y ∂μ := by
      rw [← integral_const_mul, ← integral_mul_left_eq_self (μ := μ)
        (fun y => conj (φ₂ (x : AdelicGLn.AdelicGL K n)) * h y) x]
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      simp only [hfdef, hhdef, Subgroup.coe_mul, mul_assoc, inv_mul_cancel_left]
      ring
    rw [e1]
    by_cases hx : φ₂ (x : AdelicGLn.AdelicGL K n) = 0
    · simp [hx]
    have hhi : Integrable h μ := by
      have hhc : Continuous h := (hΞ.comp (continuous_const.mul continuous_subtype_val)).mul
        (hφ₁.comp continuous_subtype_val)
      refine ⟨hhc.aestronglyMeasurable, ?_⟩
      have hb := enorm_mul_lintegral_le μ hφ₁ hφ₁l hΞ hB s x
      have hne : ‖φ₂ (x : AdelicGLn.AdelicGL K n)‖ₑ ≠ 0 := enorm_ne_zero.2 hx
      rw [HasFiniteIntegral]
      simp only [hhdef, enorm_mul]
      have hb' : (∫⁻ y, ‖Ξ (centralSection K n s * (x : AdelicGLn.AdelicGL K n)⁻¹ *
          (y : AdelicGLn.AdelicGL K n))‖ₑ * ‖φ₁ (y : AdelicGLn.AdelicGL K n)‖ₑ ∂μ) *
            ‖φ₂ (x : AdelicGLn.AdelicGL K n)‖ₑ ≤ ENNReal.ofReal (B s) * μ F := by
        rw [mul_comm]; exact hb
      have hI := (ENNReal.le_div_iff_mul_le (Or.inl hne) (Or.inl enorm_ne_top)).2 hb'
      exact lt_of_le_of_lt hI (ENNReal.div_lt_top
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hFfin.ne) hne)
    rw [integral_eq_setIntegral_tsum μ hhi, ← integral_const_mul]
    refine setIntegral_congr_fun (measurableSet_fundamentalDomain _) fun y _ => ?_
    simp only [hhdef, Subgroup.coe_mul, coe_ratElt]
    have hl : ∀ γ : GL (Fin n) K, φ₁ (AdelicGLn.diagonal K n γ * (y : AdelicGLn.AdelicGL K n)) =
        φ₁ (y : AdelicGLn.AdelicGL K n) := fun γ => hφ₁l γ _
    simp only [hl]
    rw [tsum_mul_right]
    simp only [mul_assoc]
    ring
  calc ∫ y, Ξ (centralSection K n s * (y : AdelicGLn.AdelicGL K n)) *
        matrixCoeff μ φ₁ φ₂ (y : AdelicGLn.AdelicGL K n) ∂μ
      = ∫ y, ∫ x in F, f y x ∂μ ∂μ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        simp only [matrixCoeff, hfdef]
        rw [← integral_const_mul]
    _ = ∫ x in F, ∫ y, f y x ∂μ ∂μ := integral_integral_swap hint
    _ = ∫ x in F, ∫ y in F, conj (φ₂ (x : AdelicGLn.AdelicGL K n)) * φ₁ (y : AdelicGLn.AdelicGL K n) *
          ∑' γ : GL (Fin n) K, Ξ (centralSection K n s * (x : AdelicGLn.AdelicGL K n)⁻¹ *
            AdelicGLn.diagonal K n γ * (y : AdelicGLn.AdelicGL K n)) ∂μ ∂μ :=
        setIntegral_congr_fun (measurableSet_fundamentalDomain _) fun x _ => hstep x
    _ = thetaPairing μ φ₁ φ₂ Ξ s := rfl

end Identity

section Main

variable {φ₁ φ₂ Ξ : AdelicGLn.AdelicGL K n → ℂ}

theorem matrixCoeff_centralSection_mul
    (hφ₁z : ∀ (s : {r : ℝ // 0 < r}) (x : AdelicGLn.AdelicGL K n), φ₁ (centralSection K n s * x) = φ₁ x)
    (s : {r : ℝ // 0 < r}) (g : AdelicGLn.AdelicGL K n) :
    matrixCoeff μ φ₁ φ₂ (centralSection K n s * g) = matrixCoeff μ φ₁ φ₂ g := by
  unfold matrixCoeff
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only
  rw [← mul_assoc, ← centralSection_mul_comm s (x : AdelicGLn.AdelicGL K n), mul_assoc, hφ₁z]

theorem detPow_centralSection_mul (hn : 0 < n) (s : {r : ℝ // 0 < r}) (y : normOneGL K n) (w : ℂ) :
    detPow (centralSection K n s * (y : AdelicGLn.AdelicGL K n)) w = ((s : ℝ) : ℂ) ^ w := by
  unfold detPow
  rw [map_mul, detModule_centralSection hn, mem_normOneGL_iff_detModule.1 y.2, mul_one]

theorem detPow_inv (g : AdelicGLn.AdelicGL K n) (w : ℂ) : detPow g⁻¹ w = detPow g (-w) := by
  unfold detPow
  rw [map_inv, Complex.cpow_neg]
  have hpos : (0 : ℝ) < (detModule K n g : ℝ) := (detModule K n g).2
  have e : (((detModule K n g)⁻¹ : {r : ℝ // 0 < r}) : ℝ) = ((detModule K n g : ℝ))⁻¹ := rfl
  rw [e, Complex.ofReal_inv, Complex.inv_cpow _ _ (by
    rw [Complex.arg_ofReal_of_nonneg hpos.le]; exact Real.pi_pos.ne)]

theorem stronglyMeasurable_matrixCoeff (hφ₁ : Continuous φ₁) (hφ₂ : Continuous φ₂) :
    StronglyMeasurable (matrixCoeff μ φ₁ φ₂) := by
  have hc : Continuous (Function.uncurry fun (g : AdelicGLn.AdelicGL K n) (x : normOneGL K n) =>
      φ₁ ((x : AdelicGLn.AdelicGL K n) * g) * conj (φ₂ (x : AdelicGLn.AdelicGL K n))) :=
    (hφ₁.comp ((continuous_subtype_val.comp continuous_snd).mul continuous_fst)).mul
      (Complex.continuous_conj.comp (hφ₂.comp (continuous_subtype_val.comp continuous_snd)))
  exact hc.stronglyMeasurable.integral_prod_right

theorem exists_integral_eq_mellin_thetaPairing (hn : 0 < n) (ν : Measure (AdelicGLn.AdelicGL K n))
    [ν.IsHaarMeasure] :
    ∃ c : ℝ, 0 < c ∧ ∀ (φ₁ φ₂ Ξ : AdelicGLn.AdelicGL K n → ℂ) (w : ℂ) (B : ℝ → ℝ),
      Continuous φ₁ → Continuous φ₂ → Continuous Ξ → AutomorphicForm.IsLeftInvariant φ₁ →
      (∀ (s : {r : ℝ // 0 < r}) (x : AdelicGLn.AdelicGL K n),
        φ₁ (centralSection K n s * x) = φ₁ x) →
      (∀ (t : {r : ℝ // 0 < r}) (x y : AdelicGLn.AdelicGL K n), x ∈ normOneGL K n →
        y ∈ normOneGL K n →
        Summable (fun γ : GL (Fin n) K =>
          ‖Ξ (centralSection K n t * x⁻¹ * AdelicGLn.diagonal K n γ * y)‖) ∧
        ‖φ₂ x‖ * ‖φ₁ y‖ * ∑' γ : GL (Fin n) K,
          ‖Ξ (centralSection K n t * x⁻¹ * AdelicGLn.diagonal K n γ * y)‖ ≤ B t) →
      IntegrableOn (fun t : ℝ => t ^ (w.re - 1) * B t) (Ioi 0) →
      Integrable (fun g => Ξ g * matrixCoeff μ φ₁ φ₂ g * detPow g w) ν ∧
      ∫ g, Ξ g * matrixCoeff μ φ₁ φ₂ g * detPow g w ∂ν =
        (c : ℂ) * mellin (fun t : ℝ => if h : 0 < t then thetaPairing μ φ₁ φ₂ Ξ ⟨t, h⟩ else 0) w := by
  refine ⟨centralHaarConst hn μ ν, by exact_mod_cast centralHaarConst_pos hn μ ν, ?_⟩
  intro φ₁ φ₂ Ξ w B hφ₁ hφ₂ hΞ hφ₁l hφ₁z hB hBint
  set F := fundamentalDomain (rationalGLOne K n) with hF
  have hFfin := measure_fundamentalDomain_rationalGLOne_lt_top μ
  set H : AdelicGLn.AdelicGL K n → ℂ := fun g => Ξ g * matrixCoeff μ φ₁ φ₂ g * detPow g w with hH
  have hHz : ∀ (s : {r : ℝ // 0 < r}) (y : normOneGL K n),
      H (centralSection K n s * (y : AdelicGLn.AdelicGL K n)) =
        Ξ (centralSection K n s * (y : AdelicGLn.AdelicGL K n)) *
          matrixCoeff μ φ₁ φ₂ (y : AdelicGLn.AdelicGL K n) * ((s : ℝ) : ℂ) ^ w := by
    intro s y
    simp only [hH, matrixCoeff_centralSection_mul μ hφ₁z, detPow_centralSection_mul hn]
  have hdet : Measurable fun g : AdelicGLn.AdelicGL K n => detPow g w :=
    (Complex.measurable_ofReal.comp (measurable_subtype_coe.comp
      continuous_detModule.measurable)).pow_const w
  have hHm : StronglyMeasurable H :=
    (hΞ.stronglyMeasurable.mul (stronglyMeasurable_matrixCoeff μ hφ₁ hφ₂)).mul
      hdet.stronglyMeasurable
  have hcz : Continuous fun p : normOneGL K n × {r : ℝ // 0 < r} =>
      centralSection K n p.2 * (p.1 : AdelicGLn.AdelicGL K n) :=
    (continuous_centralSection.comp continuous_snd).mul (continuous_subtype_val.comp continuous_fst)

  have hfin : ∀ s : {r : ℝ // 0 < r},
      ∫⁻ y, ‖H (centralSection K n s * (y : AdelicGLn.AdelicGL K n))‖ₑ ∂μ ≤
        ENNReal.ofReal ((s : ℝ) ^ w.re * B s) * (μ F * μ F) := by
    intro s
    have hs0 : (0 : ℝ) < s := s.2
    have hm2 : Measurable (Function.uncurry fun (y x : normOneGL K n) =>
        ‖Ξ (centralSection K n s * (y : AdelicGLn.AdelicGL K n))‖ₑ *
          ‖φ₁ ((x : AdelicGLn.AdelicGL K n) * (y : AdelicGLn.AdelicGL K n))‖ₑ *
          ‖φ₂ (x : AdelicGLn.AdelicGL K n)‖ₑ) :=
      (((hΞ.comp (continuous_const.mul (continuous_subtype_val.comp continuous_fst))).enorm.measurable).mul
        (hφ₁.comp ((continuous_subtype_val.comp continuous_snd).mul
          (continuous_subtype_val.comp continuous_fst))).enorm.measurable).mul
        (hφ₂.comp (continuous_subtype_val.comp continuous_snd)).enorm.measurable
    calc ∫⁻ y, ‖H (centralSection K n s * (y : AdelicGLn.AdelicGL K n))‖ₑ ∂μ
        ≤ ∫⁻ y, ENNReal.ofReal ((s : ℝ) ^ w.re) * ∫⁻ x in F,
            ‖Ξ (centralSection K n s * (y : AdelicGLn.AdelicGL K n))‖ₑ *
              ‖φ₁ ((x : AdelicGLn.AdelicGL K n) * (y : AdelicGLn.AdelicGL K n))‖ₑ *
              ‖φ₂ (x : AdelicGLn.AdelicGL K n)‖ₑ ∂μ ∂μ := by
          refine lintegral_mono fun y => ?_
          rw [hHz, enorm_mul, enorm_mul]
          have e1 : ‖((s : ℝ) : ℂ) ^ w‖ₑ = ENNReal.ofReal ((s : ℝ) ^ w.re) := by
            rw [← ofReal_norm, Complex.norm_cpow_eq_rpow_re_of_pos hs0]
          have e2 : ‖matrixCoeff μ φ₁ φ₂ (y : AdelicGLn.AdelicGL K n)‖ₑ ≤ ∫⁻ x in F,
              ‖φ₁ ((x : AdelicGLn.AdelicGL K n) * (y : AdelicGLn.AdelicGL K n))‖ₑ *
                ‖φ₂ (x : AdelicGLn.AdelicGL K n)‖ₑ ∂μ := by
            refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
            refine lintegral_congr fun x => ?_
            rw [enorm_mul, RCLike.enorm_conj]
          rw [e1]
          calc ‖Ξ (centralSection K n s * (y : AdelicGLn.AdelicGL K n))‖ₑ *
                ‖matrixCoeff μ φ₁ φ₂ (y : AdelicGLn.AdelicGL K n)‖ₑ * ENNReal.ofReal ((s : ℝ) ^ w.re)
              ≤ ‖Ξ (centralSection K n s * (y : AdelicGLn.AdelicGL K n))‖ₑ *
                (∫⁻ x in F, ‖φ₁ ((x : AdelicGLn.AdelicGL K n) * (y : AdelicGLn.AdelicGL K n))‖ₑ *
                  ‖φ₂ (x : AdelicGLn.AdelicGL K n)‖ₑ ∂μ) * ENNReal.ofReal ((s : ℝ) ^ w.re) := by
                gcongr
            _ = ENNReal.ofReal ((s : ℝ) ^ w.re) * ∫⁻ x in F,
                ‖Ξ (centralSection K n s * (y : AdelicGLn.AdelicGL K n))‖ₑ *
                  ‖φ₁ ((x : AdelicGLn.AdelicGL K n) * (y : AdelicGLn.AdelicGL K n))‖ₑ *
                  ‖φ₂ (x : AdelicGLn.AdelicGL K n)‖ₑ ∂μ := by
                rw [mul_comm _ (ENNReal.ofReal _), ← lintegral_const_mul' _ _ enorm_ne_top]
                congr 1
                refine lintegral_congr fun x => ?_
                ring
      _ = ENNReal.ofReal ((s : ℝ) ^ w.re) * ∫⁻ x in F, ∫⁻ y,
            ‖Ξ (centralSection K n s * (y : AdelicGLn.AdelicGL K n))‖ₑ *
              ‖φ₁ ((x : AdelicGLn.AdelicGL K n) * (y : AdelicGLn.AdelicGL K n))‖ₑ *
              ‖φ₂ (x : AdelicGLn.AdelicGL K n)‖ₑ ∂μ ∂μ := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            lintegral_lintegral_swap hm2.aemeasurable]
      _ ≤ ENNReal.ofReal ((s : ℝ) ^ w.re) * (ENNReal.ofReal (B s) * μ F * μ F) := by
          gcongr
          exact lintegral_lintegral_enorm_le μ hφ₁ hφ₁l hΞ hB s
      _ = ENNReal.ofReal ((s : ℝ) ^ w.re * B s) * (μ F * μ F) := by
          rw [ENNReal.ofReal_mul (Real.rpow_nonneg hs0.le _)]
          ring

  have hint : Integrable H ν := by
    rw [integrable_iff_prod μ ν hn H]
    refine ⟨(hHm.comp_measurable hcz.measurable).aestronglyMeasurable, ?_⟩
    rw [HasFiniteIntegral, lintegral_prod_symm (fun p : normOneGL K n × {r : ℝ // 0 < r} =>
      ‖H (centralSection K n p.2 * (p.1 : AdelicGLn.AdelicGL K n))‖ₑ)
      (hHm.comp_measurable hcz.measurable).enorm.aemeasurable]
    refine lt_of_le_of_lt (lintegral_mono fun s => hfin s) ?_
    rw [lintegral_mul_const' _ _ (ENNReal.mul_ne_top hFfin.ne hFfin.ne)]
    refine ENNReal.mul_lt_top ?_ (ENNReal.mul_lt_top hFfin hFfin)
    rw [lintegral_posRealMeasure (fun t => ENNReal.ofReal (t ^ w.re * B t))]
    have e3 : ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal t⁻¹ * ENNReal.ofReal (t ^ w.re * B t) =
        ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ (w.re - 1) * B t) := by
      refine setLIntegral_congr_fun measurableSet_Ioi fun t (ht : 0 < t) => ?_
      rw [← ENNReal.ofReal_mul (inv_nonneg.2 ht.le), Real.rpow_sub_one ht.ne']
      congr 1
      field_simp
    rw [e3]
    refine lt_of_le_of_lt (lintegral_mono fun t => ?_) hBint.2
    rw [Real.enorm_eq_ofReal_abs]
    exact ENNReal.ofReal_le_ofReal (le_abs_self _)
  refine ⟨hint, ?_⟩
  rw [integral_eq_centralHaarConst_smul hn μ ν hint]
  have hinner : ∀ s : {r : ℝ // 0 < r},
      ∫ y, H (centralSection K n s * (y : AdelicGLn.AdelicGL K n)) ∂μ =
        thetaPairing μ φ₁ φ₂ Ξ s * ((s : ℝ) : ℂ) ^ w := by
    intro s
    simp_rw [hHz]
    rw [integral_mul_const, integral_mul_matrixCoeff_eq_thetaPairing μ hφ₁ hφ₂ hφ₁l hΞ hB s]
  simp_rw [hinner]
  set J' : ℝ → ℂ := fun t => if h : 0 < t then thetaPairing μ φ₁ φ₂ Ξ ⟨t, h⟩ * (t : ℂ) ^ w else 0
    with hJ'
  have e4 : (fun s : {r : ℝ // 0 < r} => thetaPairing μ φ₁ φ₂ Ξ s * ((s : ℝ) : ℂ) ^ w) =
      fun s : {r : ℝ // 0 < r} => J' (s : ℝ) := by
    funext s
    simp only [hJ', dif_pos s.2, Subtype.coe_eta]
  rw [e4, integral_posRealMeasure, Complex.real_smul, mellin]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun t (ht : 0 < t) => ?_
  simp only [hJ', dif_pos ht]
  rw [Complex.real_smul, smul_eq_mul, Complex.cpow_sub _ _ (Complex.ofReal_ne_zero.2 ht.ne'),
    Complex.cpow_one, Complex.ofReal_inv]
  have : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 ht.ne'
  field_simp

end Main

end GJGlobal

end

end GroundTheory.Automorphic
