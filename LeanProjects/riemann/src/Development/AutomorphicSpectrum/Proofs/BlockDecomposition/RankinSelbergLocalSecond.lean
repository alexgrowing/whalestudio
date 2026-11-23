import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerLocalTateIntegral

noncomputable section

open MeasureTheory GroundTheory.LocalField Ad3 Ad3.R
open scoped ValuativeRel ENNReal NNReal Convolution

namespace GlobalTheory.CompanionTheory.RSLocal

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

theorem selfDual_eq {ψ : AddChar F Circle} (hψ : IsStd ψ) : selfDualMeasure ψ = haarIntegers F := by
  unfold selfDualMeasure
  rw [hψ.2.2]
  simp

theorem integral_units (G : F → ℂ) :
    ∫ a : Fˣ, G a * mp a 1 ∂multHaar F = ((multHaarConst F).toReal : ℂ) * ∫ t, G t ∂haarIntegers F := by
  have h := integral_multHaar (K := F) (fun x => G x * ((modulus x : ℝ) : ℂ) ^ (1 : ℂ))
  simp only [mp]
  rw [h]
  have e : ∫ x in ({0} : Set F)ᶜ, ((modulus x : ℝ))⁻¹ • (G x * ((modulus x : ℝ) : ℂ) ^ (1 : ℂ)) ∂haarIntegers F =
      ∫ x in ({0} : Set F)ᶜ, G x ∂haarIntegers F := by
    refine setIntegral_congr_fun (measurableSet_singleton 0).compl fun x hx => ?_
    have hm : ((modulus x : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (modulus_ne_zero hx)
    simp only [Complex.cpow_one, Complex.real_smul]
    push_cast
    field_simp
  rw [e, Measure.restrict_eq_self_of_ae_mem, Complex.real_smul]
  exact (measure_eq_zero_iff_ae_notMem.mp haarIntegers_singleton_zero).mono fun x hx => hx

theorem measurable_chF {c : Fˣ →* ℂˣ} (hc : Continuous c) (s : ℂ) : Measurable (chF c s) := by
  have hg : Continuous fun u : Fˣ => ((c u : ℂˣ) : ℂ) * mp u s := by
    refine (Units.continuous_val.comp hc).mul ?_
    refine (Complex.continuous_ofReal.comp (NNReal.continuous_coe.comp
      (continuous_modulus.comp Units.continuous_val))).cpow continuous_const fun u => ?_
    exact Complex.ofReal_mem_slitPlane.mpr (by exact_mod_cast modulus_pos u.ne_zero)
  have e : chF c s = Function.extend (Units.val : Fˣ → F) (fun u => ((c u : ℂˣ) : ℂ) * mp u s) (fun _ => 0) := by
    funext t
    by_cases ht : t = 0
    · subst ht
      rw [Function.extend_apply' _ _ _ (by rintro ⟨u, hu⟩; exact u.ne_zero hu)]
      simp [chF]
    · have := Units.val_injective.extend_apply (f := (Units.val : Fˣ → F)) (fun u => ((c u : ℂˣ) : ℂ) * mp u s) (fun _ => (0 : ℂ)) (Units.mk0 t ht)
      rw [Units.val_mk0] at this
      rw [this]
      simp [chF, ht]
  rw [e]
  exact measurableEmbedding_units_val.measurable_extend hg.measurable measurable_const

theorem integrable_of_units {G : F → ℂ} (hG : Measurable G)
    (h : Integrable (fun a : Fˣ => G a * mp a 1) (multHaar F)) : Integrable G (haarIntegers F) := by
  refine ⟨hG.aestronglyMeasurable, ?_⟩
  have h2 := h.2
  unfold HasFiniteIntegral at h2 ⊢
  have hm : Measurable fun x : F => ‖G x‖ₑ * (modulus x : ℝ≥0∞) :=
    hG.enorm.mul measurable_modulus.coe_nnreal_ennreal
  have e1 : ∫⁻ a : Fˣ, ‖G a * mp a 1‖ₑ ∂multHaar F = ∫⁻ a : Fˣ, (fun x : F => ‖G x‖ₑ * (modulus x : ℝ≥0∞)) a ∂multHaar F := by
    refine lintegral_congr fun a => ?_
    simp only [mp, Complex.cpow_one]
    rw [enorm_mul, ← ofReal_norm (((modulus (a : F) : ℝ) : ℂ)), Complex.norm_real, Real.norm_of_nonneg (NNReal.coe_nonneg _), ENNReal.ofReal_coe_nnreal]
  rw [e1, lintegral_multHaar hm] at h2
  have e2 : ∫⁻ x in ({0} : Set F)ᶜ, ((modulus x : ℝ≥0∞))⁻¹ * (‖G x‖ₑ * (modulus x : ℝ≥0∞)) ∂haarIntegers F =
      ∫⁻ x in ({0} : Set F)ᶜ, ‖G x‖ₑ ∂haarIntegers F := by
    refine setLIntegral_congr_fun (measurableSet_singleton 0).compl fun x hx => ?_
    have h0 : (modulus x : ℝ≥0∞) ≠ 0 := ENNReal.coe_ne_zero.mpr (modulus_ne_zero hx)
    rw [mul_comm, mul_assoc, ENNReal.mul_inv_cancel h0 ENNReal.coe_ne_top, mul_one]
  rw [e2, Measure.restrict_eq_self_of_ae_mem] at h2
  · exact (ENNReal.mul_lt_top_iff.mp h2).elim (fun h => h.2) (fun h => h.elim (fun h => absurd h multHaarConst_ne_zero) (fun h => by simp [h]))
  · exact (measure_eq_zero_iff_ae_notMem.mp haarIntegers_singleton_zero).mono fun x hx => hx

def conv (μ : Measure F) (g₁ g₃ : F → ℂ) (τ : F) : ℂ := ∫ x, g₁ x * g₃ (τ - x) ∂μ

theorem conv_mem (μ : Measure F) {g₁ g₃ : F → ℂ} (h₁ : g₁ ∈ schwartzBruhat F) (h₃ : g₃ ∈ schwartzBruhat F) :
    conv μ g₁ g₃ ∈ schwartzBruhat F := by
  obtain ⟨-, M₁, -, hM₁⟩ := exists_invariant_of_mem_schwartzBruhat h₁
  obtain ⟨N, M₃, hN, hM₃⟩ := exists_invariant_of_mem_schwartzBruhat h₃
  refine ⟨isLocallyConstant_of_add_valBall (N := N) fun τ h hh => ?_,
    HasCompactSupport.intro (isCompact_valBall (min M₁ M₃)) fun τ hτ => ?_⟩
  · unfold conv
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    have := hN (τ - x) h hh
    show g₁ x * g₃ (τ + h - x) = g₁ x * g₃ (τ - x)
    rw [show τ + h - x = τ - x + h by ring, this]
  · have : (fun x => g₁ x * g₃ (τ - x)) = fun _ => 0 := by
      funext x
      by_contra hne
      have a₁ : g₁ x ≠ 0 := left_ne_zero_of_mul hne
      have a₃ : g₃ (τ - x) ≠ 0 := right_ne_zero_of_mul hne
      apply hτ
      have b₁ := valBall_antitone (min_le_left M₁ M₃) (hM₁ _ a₁)
      have b₃ := valBall_antitone (min_le_right M₁ M₃) (hM₃ _ a₃)
      have := add_mem b₁ b₃
      rwa [add_sub_cancel] at this
    unfold conv
    rw [this]
    simp

theorem conv_fourier (μ : Measure F) [μ.IsAddHaarMeasure] {ψ : AddChar F Circle} (hψ : Continuous ψ)
    {g₁ g₃ : F → ℂ} (h₁ : g₁ ∈ schwartzBruhat F) (h₃ : g₃ ∈ schwartzBruhat F) (a : F) :
    localFourier μ ψ (conv μ g₁ g₃) a = localFourier μ ψ g₁ a * localFourier μ ψ g₃ a := by
  have i₁ := integrable_mul_char_of_mem_schwartzBruhat μ hψ h₁ a
  have i₃ := integrable_mul_char_of_mem_schwartzBruhat μ hψ h₃ a
  have key := integral_convolution (L := ContinuousLinearMap.mul ℂ ℂ) (μ := μ) (ν := μ) i₁ i₃
  have e : ∀ τ, ((fun x => g₁ x * (ψ (x * a) : ℂ)) ⋆[ContinuousLinearMap.mul ℂ ℂ, μ] (fun x => g₃ x * (ψ (x * a) : ℂ))) τ =
      conv μ g₁ g₃ τ * (ψ (τ * a) : ℂ) := by
    intro τ
    rw [convolution_def]
    unfold conv
    rw [← integral_mul_const]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    have : (ψ (τ * a) : ℂ) = (ψ (x * a) : ℂ) * (ψ ((τ - x) * a) : ℂ) := by
      rw [← Circle.coe_mul, ← AddChar.map_add_eq_mul]
      congr 2
      ring
    simp only [ContinuousLinearMap.mul_apply']
    rw [this]
    ring
  simp only [e] at key
  exact key

theorem conv_pair (μ : Measure F) [μ.IsAddHaarMeasure] {g₁ g₃ k : F → ℂ}
    (hi : Integrable (fun p : F × F => g₁ p.1 * g₃ (p.2 - p.1) * k p.2) (μ.prod μ)) :
    ∫ τ, conv μ g₁ g₃ τ * k τ ∂μ = ∫ p : F × F, g₁ p.1 * g₃ p.2 * k (p.1 + p.2) ∂(μ.prod μ) := by
  have mpr := measurePreserving_prod_add μ μ
  have he : MeasurableEmbedding (fun z : F × F => (z.1, z.1 + z.2)) :=
    (MeasurableEquiv.shearAddRight F).measurableEmbedding
  have h1 := mpr.integral_comp he (fun p : F × F => g₁ p.1 * g₃ (p.2 - p.1) * k p.2)
  have h2 := integral_prod_symm _ hi
  simp only [add_sub_cancel_left] at h1
  rw [h1, h2]
  refine integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
  simp only [conv]
  rw [integral_mul_const]

theorem integrable_phi (μ : Measure F) [μ.IsAddHaarMeasure] {g₁ g₃ k : F → ℂ} (hk : Measurable k)
    (h₁ : g₁ ∈ schwartzBruhat F) (h₃ : g₃ ∈ schwartzBruhat F)
    (hb : ∀ M : ℤ, Integrable (fun τ => (valBall F M : Set F).indicator (fun _ => (1 : ℂ)) τ * k τ) μ) :
    Integrable (fun p : F × F => g₁ p.1 * g₃ (p.2 - p.1) * k p.2) (μ.prod μ) := by
  obtain ⟨-, M₁, -, hM₁⟩ := exists_invariant_of_mem_schwartzBruhat h₁
  obtain ⟨-, M₃, -, hM₃⟩ := exists_invariant_of_mem_schwartzBruhat h₃
  obtain ⟨C, hC⟩ := h₃.1.continuous.bounded_above_of_compact_support h₃.2
  have i₁ : Integrable g₁ μ := h₁.1.continuous.integrable_of_hasCompactSupport h₁.2
  have i := i₁.mul_prod (hb (min M₁ M₃))
  have c₃ : Continuous fun p : F × F => g₃ (p.2 - p.1) :=
    h₃.1.continuous.comp (continuous_snd.sub continuous_fst)
  have := i.bdd_mul (c := C) c₃.aestronglyMeasurable (Filter.Eventually.of_forall fun p => hC _)
  refine this.congr (Filter.Eventually.of_forall fun p => ?_)
  by_cases a₁ : g₁ p.1 = 0
  · simp [a₁]
  by_cases a₃ : g₃ (p.2 - p.1) = 0
  · simp [a₃]
  have b₁ := valBall_antitone (min_le_left M₁ M₃) (hM₁ _ a₁)
  have b₃ := valBall_antitone (min_le_right M₁ M₃) (hM₃ _ a₃)
  have hm : p.2 ∈ (valBall F (min M₁ M₃) : Set F) := by
    have := add_mem b₁ b₃
    rwa [add_sub_cancel] at this
  simp only [Set.indicator_of_mem hm]
  ring

theorem isUnit1_inv {c : Fˣ →* ℂˣ} (hc : IsUnit1 c) : IsUnit1 c⁻¹ := by
  refine ⟨continuous_quasiChar_inv hc.1, fun x => ?_⟩
  have := hc.2 x
  simp [this]

theorem chF_units (c : Fˣ →* ℂˣ) (s : ℂ) (u : Fˣ) :
    chF c s u * mp u 1 = ((c u : ℂˣ) : ℂ) * ((modulus (u : F) : ℝ) : ℂ) ^ (s + 1) := by
  have hm : ((modulus (u : F) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (modulus_ne_zero u.ne_zero)
  simp only [chF, u.ne_zero, dite_false, Units.mk0_val, mp]
  rw [Complex.cpow_add _ _ hm, mul_assoc]

theorem integrable_ball {c : Fˣ →* ℂˣ} (hc : IsUnit1 c) {s : ℂ} (hs : Strip s) (M : ℤ) :
    Integrable (fun τ => (valBall F M : Set F).indicator (fun _ => (1 : ℂ)) τ * chF c⁻¹ (-s) τ)
      (haarIntegers F) := by
  have hc' := isUnit1_inv hc
  have hb : (valBall F M : Set F).indicator (fun _ => (1 : ℂ)) ∈ schwartzBruhat F :=
    indicator_valBall_mem_schwartzBruhat M
  have hz := integrable_localZeta hb hc'.1 (s := 1 - s) (by
    rw [GlobalTheory.CompanionTheory.TateFE.quasiCharExponent_eq_zero_of_unit hc']
    have := hs.2
    simp
    linarith)
  refine integrable_of_units ((measurable_const.indicator (measurableSet_valBall M)).mul
    (measurable_chF hc'.1 _)) (hz.congr (Filter.Eventually.of_forall fun u => ?_))
  show _ * _ * _ = _ * _ * _
  rw [mul_assoc ((valBall F M : Set F).indicator (fun _ => (1 : ℂ)) (u : F)) (chF _ _ _), chF_units, mul_assoc,
    neg_add_eq_sub]

theorem main_conv {ψ : AddChar F Circle} (hψ : IsStd ψ) {c : Fˣ →* ℂˣ} (hc : IsUnit1 c) {s : ℂ} (hs : Strip s)
    {g₁ g₃ : F → ℂ} (h₁ : g₁ ∈ schwartzBruhat F) (h₃ : g₃ ∈ schwartzBruhat F) :
    ∫ a : Fˣ, localFourier (selfDualMeasure ψ) ψ g₁ a * localFourier (selfDualMeasure ψ) ψ g₃ a *
        ((c a : ℂˣ) : ℂ) * mp a s ∂multHaar F =
      ((multHaarConst F).toReal : ℂ) * gam ψ c⁻¹ (1 - s) *
        ∫ p : F × F, g₁ p.1 * g₃ p.2 * chF c⁻¹ (-s) (p.1 + p.2) ∂((selfDualMeasure ψ).prod (selfDualMeasure ψ)) := by
  have hc' := isUnit1_inv hc
  have hh := conv_mem (selfDualMeasure ψ) h₁ h₃
  have ff := GlobalTheory.CompanionTheory.TateFE.first_form hψ hc' hh (s := 1 - s) (by have := hs.2; simp; linarith)
    (by have := hs.1; simp; linarith)
  rw [inv_inv, sub_sub_cancel] at ff
  have e1 : localZeta (localFourier (selfDualMeasure ψ) ψ (conv (selfDualMeasure ψ) g₁ g₃)) c s =
      ∫ a : Fˣ, localFourier (selfDualMeasure ψ) ψ g₁ a * localFourier (selfDualMeasure ψ) ψ g₃ a *
        ((c a : ℂˣ) : ℂ) * mp a s ∂multHaar F := by
    unfold localZeta
    refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
    show _ * _ * _ = _ * _ * _ * _
    rw [conv_fourier _ hψ.1 h₁ h₃]
    rfl
  have e2 : localZeta (conv (selfDualMeasure ψ) g₁ g₃) c⁻¹ (1 - s) =
      ((multHaarConst F).toReal : ℂ) * ∫ τ, conv (selfDualMeasure ψ) g₁ g₃ τ * chF c⁻¹ (-s) τ ∂selfDualMeasure ψ := by
    have := integral_units (F := F) (fun τ => conv (selfDualMeasure ψ) g₁ g₃ τ * chF c⁻¹ (-s) τ)
    rw [← selfDual_eq hψ] at this
    rw [← this]
    unfold localZeta
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    show _ * _ * _ = _ * _ * _
    rw [mul_assoc (conv _ _ _ _) (chF _ _ _), chF_units, mul_assoc, neg_add_eq_sub]
  have e3 := conv_pair (selfDualMeasure ψ) (integrable_phi (selfDualMeasure ψ) (measurable_chF hc'.1 (-s)) h₁ h₃
    (fun M => by rw [selfDual_eq hψ]; exact integrable_ball hc hs M))
  rw [← e1, ff, e2, e3]
  ring

theorem fourier_scale (μ : Measure F) [μ.IsAddHaarMeasure] (ψ : AddChar F Circle) (b : Fˣ) (f : F → ℂ) (w : F) :
    ∫ y, f y * (ψ (y * w) : ℂ) ∂μ =
      ((modulus (b : F) : ℝ) : ℂ) * localFourier μ ψ (fun x => f (b * x)) (b * w) := by
  have h := integral_comp_mul_left μ b.ne_zero (fun y => f y * (ψ (y * w) : ℂ))
  have hm : ((modulus (b : F) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (modulus_ne_zero b.ne_zero)
  have e : localFourier μ ψ (fun x => f (b * x)) (b * w) = ∫ x, f (b * x) * (ψ (b * x * w) : ℂ) ∂μ := by
    unfold localFourier
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show _ * _ = _ * _
    rw [show x * (b * w) = b * x * w by ring]
  rw [e, h, Complex.real_smul]
  push_cast
  rw [← mul_assoc, mul_inv_cancel₀ hm, one_mul]

theorem prod_scale (μ : Measure F) [μ.IsAddHaarMeasure] (b₁ b₃ : Fˣ) (H : F × F → ℂ) :
    ∫ p, H p ∂(μ.prod μ) = ((modulus (b₁ : F) : ℝ) : ℂ) * ((modulus (b₃ : F) : ℝ) : ℂ) *
      ∫ p : F × F, H ((b₁ : F) * p.1, (b₃ : F) * p.2) ∂(μ.prod μ) := by
  have he : MeasurableEmbedding (Prod.map (fun x : F => (b₁ : F) * x) (fun x : F => (b₃ : F) * x)) :=
    ((Homeomorph.mulLeft₀ (b₁ : F) b₁.ne_zero).prodCongr (Homeomorph.mulLeft₀ (b₃ : F) b₃.ne_zero)).measurableEmbedding
  have hm : Measure.map (Prod.map (fun x : F => (b₁ : F) * x) (fun x : F => (b₃ : F) * x)) (μ.prod μ) =
      ((modulus (b₁ : F))⁻¹ * (modulus (b₃ : F))⁻¹) • μ.prod μ := by
    rw [← Measure.map_prod_map _ _ (measurable_const_mul _) (measurable_const_mul _),
      map_mul_left_eq_smul μ b₁.ne_zero, map_mul_left_eq_smul μ b₃.ne_zero, Measure.prod_smul_left,
      Measure.prod_smul_right, smul_smul]
  have h := he.integral_map (μ := μ.prod μ) H
  rw [hm, integral_smul_nnreal_measure] at h
  have m₁ : ((modulus (b₁ : F) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (modulus_ne_zero b₁.ne_zero)
  have m₃ : ((modulus (b₃ : F) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (modulus_ne_zero b₃.ne_zero)
  have h' : ∫ p : F × F, H ((b₁ : F) * p.1, (b₃ : F) * p.2) ∂(μ.prod μ) =
      ((modulus (b₁ : F) : ℝ) : ℂ)⁻¹ * ((modulus (b₃ : F) : ℝ) : ℂ)⁻¹ * ∫ p, H p ∂(μ.prod μ) := by
    have := h.symm
    simp only [Prod.map] at this
    rw [this, NNReal.smul_def, Complex.real_smul]
    push_cast
    rfl
  rw [h']
  field_simp

theorem scale_mem {f : F → ℂ} (hf : f ∈ schwartzBruhat F) (b : Fˣ) : (fun x => f (b * x)) ∈ schwartzBruhat F :=
  ⟨hf.1.comp_continuous (continuous_const.mul continuous_id),
    hf.2.comp_homeomorph (Homeomorph.mulLeft₀ (b : F) b.ne_zero)⟩

theorem a2 : A2 := by
  intro F _ _ _ _ _ _ ψ hψ
  refine ⟨((multHaarConst F).toReal : ℂ), ?_, fun G => ?_, ?_⟩
  · have : (multHaarConst F).toReal ≠ 0 := ENNReal.toReal_ne_zero.mpr ⟨multHaarConst_ne_zero, multHaarConst_ne_top⟩
    exact_mod_cast this
  · rw [selfDual_eq hψ]
    exact integral_units G
  · intro f₁ h₁ f₃ h₃ u₁ u₃ c hc s hs
    have L := main_conv hψ hc hs (scale_mem h₁ (-u₁)) (scale_mem h₃ u₃)
    have hR := prod_scale (selfDualMeasure ψ) (-u₁) u₃
      (fun p => f₁ p.1 * f₃ p.2 * chF c⁻¹ (-s) (p.2 * (u₃⁻¹ : Fˣ) - p.1 * (u₁⁻¹ : Fˣ)))
    have hA : ∀ a : Fˣ, ∫ y, f₁ y * (ψ (-(y * a * (u₁⁻¹ : Fˣ))) : ℂ) ∂selfDualMeasure ψ =
        ((modulus ((-u₁ : Fˣ) : F) : ℝ) : ℂ) * localFourier (selfDualMeasure ψ) ψ (fun x => f₁ ((-u₁ : Fˣ) * x)) a := by
      intro a
      have := fourier_scale (selfDualMeasure ψ) ψ (-u₁) f₁ (-((a : F) * (u₁⁻¹ : Fˣ)))
      have e : ((-u₁ : Fˣ) : F) * (-((a : F) * (u₁⁻¹ : Fˣ))) = a := by
        rw [Units.val_neg, neg_mul_neg, mul_left_comm, Units.mul_inv, mul_one]
      rw [e] at this
      rw [← this]
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      show _ * _ = _ * _
      rw [show -(y * (a : F) * ((u₁⁻¹ : Fˣ) : F)) = y * -((a : F) * ((u₁⁻¹ : Fˣ) : F)) by ring]
    have hB : ∀ a : Fˣ, ∫ y, f₃ y * (ψ (y * a * (u₃⁻¹ : Fˣ)) : ℂ) ∂selfDualMeasure ψ =
        ((modulus (u₃ : F) : ℝ) : ℂ) * localFourier (selfDualMeasure ψ) ψ (fun x => f₃ (u₃ * x)) a := by
      intro a
      have := fourier_scale (selfDualMeasure ψ) ψ u₃ f₃ ((a : F) * (u₃⁻¹ : Fˣ))
      have e : (u₃ : F) * ((a : F) * (u₃⁻¹ : Fˣ)) = a := by
        rw [mul_left_comm, Units.mul_inv, mul_one]
      rw [e] at this
      rw [← this]
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      show _ * _ = _ * _
      rw [mul_assoc]
    simp only [hA, hB]
    rw [hR]
    have e : (fun a : Fˣ => ((modulus ((-u₁ : Fˣ) : F) : ℝ) : ℂ) * localFourier (selfDualMeasure ψ) ψ (fun x => f₁ ((-u₁ : Fˣ) * x)) a *
          (((modulus (u₃ : F) : ℝ) : ℂ) * localFourier (selfDualMeasure ψ) ψ (fun x => f₃ (u₃ * x)) a) * ((c a : ℂˣ) : ℂ) * mp a s) =
        fun a : Fˣ => (((modulus ((-u₁ : Fˣ) : F) : ℝ) : ℂ) * ((modulus (u₃ : F) : ℝ) : ℂ)) *
          (localFourier (selfDualMeasure ψ) ψ (fun x => f₁ ((-u₁ : Fˣ) * x)) a *
            localFourier (selfDualMeasure ψ) ψ (fun x => f₃ (u₃ * x)) a * ((c a : ℂˣ) : ℂ) * mp a s) := by
      funext a
      ring
    rw [e, integral_const_mul, L]
    have e' : (fun p : F × F => f₁ (((-u₁ : Fˣ) : F) * p.1) * f₃ ((u₃ : F) * p.2) *
          chF c⁻¹ (-s) ((u₃ : F) * p.2 * (u₃⁻¹ : Fˣ) - ((-u₁ : Fˣ) : F) * p.1 * (u₁⁻¹ : Fˣ))) =
        fun p : F × F => f₁ (((-u₁ : Fˣ) : F) * p.1) * f₃ ((u₃ : F) * p.2) * chF c⁻¹ (-s) (p.1 + p.2) := by
      funext p
      have a₁ : (u₁ : F) * (u₁⁻¹ : Fˣ) = 1 := Units.mul_inv u₁
      have a₃ : (u₃ : F) * (u₃⁻¹ : Fˣ) = 1 := Units.mul_inv u₃
      have : (u₃ : F) * p.2 * (u₃⁻¹ : Fˣ) - ((-u₁ : Fˣ) : F) * p.1 * (u₁⁻¹ : Fˣ) = p.1 + p.2 := by
        rw [Units.val_neg]
        linear_combination p.2 * a₃ + p.1 * a₁
      rw [this]
    simp only [] at e' ⊢
    rw [e']
    ring

end GlobalTheory.CompanionTheory.RSLocal

end
