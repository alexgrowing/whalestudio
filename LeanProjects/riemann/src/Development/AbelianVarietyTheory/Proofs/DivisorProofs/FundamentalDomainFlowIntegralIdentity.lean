import Mathlib
open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace GlobalTheory.RightTranslationL2Continuity

variable {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H]
  [SecondCountableTopology H] [T2Space H] [MeasurableSpace H] [BorelSpace H]

theorem setLIntegral_mul_right (μ : Measure H) [μ.IsHaarMeasure] (Γ : Subgroup H) [Countable Γ]
    {𝓕 : Set H} (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) (F : H → ℝ≥0∞)
    (hF : ∀ g ∈ Γ, ∀ x, F (g * x) = F x) (h : H) :
    ∫⁻ x in 𝓕, F (x * h) ∂μ = (Measure.modularCharacterFun h : ℝ≥0∞) * ∫⁻ x in 𝓕, F x ∂μ := by
  let e : H ≃ᵐ H := MeasurableEquiv.mulRight h
  let T : Set H := (fun y => y * h⁻¹) ⁻¹' 𝓕
  have hq : Measure.QuasiMeasurePreserving (fun y : H => y * h⁻¹) μ μ :=
    ⟨measurable_mul_const _, by
      rw [Measure.map_right_mul_eq_modularCharacterFun_smul]
      exact Measure.smul_absolutelyContinuous⟩
  have hT : IsFundamentalDomain Γ T μ :=
    h𝓕.preimage_of_equiv hq (e := id) Function.bijective_id (fun g x => by
      simp [Subgroup.smul_def, smul_eq_mul, mul_assoc])
  have heT : e ⁻¹' T = 𝓕 := by
    ext x; simp [T, e]
  have hmap : μ.map e = Measure.modularCharacterFun h • μ :=
    Measure.map_right_mul_eq_modularCharacterFun_smul μ h
  calc ∫⁻ x in 𝓕, F (x * h) ∂μ = ∫⁻ y, F y ∂((μ.restrict 𝓕).map e) :=
        (lintegral_map_equiv F e).symm
    _ = ∫⁻ y, F y ∂((μ.map e).restrict T) := by rw [e.restrict_map μ T, heT]
    _ = (Measure.modularCharacterFun h : ℝ≥0∞) * ∫⁻ y in T, F y ∂μ := by
        rw [hmap, Measure.restrict_smul, lintegral_smul_measure]
        rfl
    _ = _ := by rw [hT.setLIntegral_eq h𝓕 F (fun g x => hF g g.2 x)]

theorem enorm_sub_sq_le (a b : ℂ) : ‖a - b‖ₑ ^ 2 ≤ 2 * ‖a‖ₑ ^ 2 + 2 * ‖b‖ₑ ^ 2 := by
  have h : ‖a - b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
    nlinarith [norm_sub_le a b, norm_nonneg a, norm_nonneg b, norm_nonneg (a - b),
      sq_nonneg (‖a‖ - ‖b‖)]
  rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm,
    ← ENNReal.ofReal_pow (norm_nonneg _), ← ENNReal.ofReal_pow (norm_nonneg _),
    ← ENNReal.ofReal_pow (norm_nonneg _)]
  calc ENNReal.ofReal (‖a - b‖ ^ 2) ≤ ENNReal.ofReal (2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2) :=
        ENNReal.ofReal_le_ofReal h
    _ = _ := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by norm_num),
          ENNReal.ofReal_mul (by norm_num)]
        norm_num

theorem lt_toReal_of_ofReal_lt {a : ℝ} {b : ℝ≥0∞} (hb : b ≠ ∞) (h : ENNReal.ofReal a < b) :
    a < b.toReal := by
  have h1 : (ENNReal.ofReal a).toReal < b.toReal := ENNReal.toReal_strict_mono hb h
  rw [ENNReal.toReal_ofReal'] at h1
  exact lt_of_le_of_lt (le_max_left _ _) h1

theorem tendsto_eLpNorm_mul_right_sub (μ : Measure H) [μ.IsHaarMeasure] (Γ : Subgroup H)
    [Countable Γ] (𝓕 : Set H) (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) (γ : Multiplicative ℝ →* H)
    (hγ : Continuous γ) (f₁ : H → ℂ) (hf : Continuous f₁)
    (hinv : ∀ g ∈ Γ, ∀ x, f₁ (g * x) = f₁ x) (hint : IntegrableOn (fun x => ‖f₁ x‖ ^ 2) 𝓕 μ) :
    Tendsto (fun s : ℝ => eLpNorm (fun x => f₁ (x * γ (Multiplicative.ofAdd s)) - f₁ x) 2
      (μ.restrict 𝓕)) (𝓝 0) (𝓝 0) := by
  set ν := μ.restrict 𝓕 with hν
  set hs : ℝ → H := fun s => γ (Multiplicative.ofAdd s) with hhs
  have hsc : Continuous hs := hγ.comp continuous_ofAdd
  have hs0 : hs 0 = 1 := by simp [hs]
  set Δ : ℝ → ℝ≥0 := fun s => Measure.modularCharacterFun (hs s) with hΔ
  have hΔneg : ∀ s, (Δ (-s) : ℝ) * Δ s = 1 := fun s => by
    have : hs (-s) * hs s = 1 := by
      simp only [hs, ← map_mul, ← ofAdd_add, neg_add_cancel, ofAdd_zero, map_one]
    have h2 := Measure.modularCharacterFun_map_mul (hs (-s)) (hs s)
    rw [this, Measure.modularCharacterFun_map_one] at h2
    simp only [Δ]
    exact_mod_cast h2.symm
  set N : H → ℝ≥0∞ := fun x => ‖f₁ x‖ₑ ^ 2 with hN
  set I : ℝ≥0∞ := ∫⁻ x, N x ∂ν with hIdef
  have hI : I ≠ ∞ := by
    have := hint.hasFiniteIntegral
    unfold HasFiniteIntegral at this
    refine ne_of_lt (lt_of_le_of_lt (le_of_eq (lintegral_congr fun x => ?_)) this)
    simp [N, enorm_pow]
  have hNm : ∀ h : H, Measurable fun x => N (x * h) := fun h =>
    (hf.measurable.comp (measurable_mul_const h)).enorm.pow_const 2
  have hnorm : ∀ s, ∫⁻ x, N (x * hs s) ∂ν = Δ s * I := fun s =>
    setLIntegral_mul_right μ Γ h𝓕 N (fun g hg x => by simp only [N, hinv g hg x]) (hs s)
  have hpt : ∀ x, Tendsto (fun s => f₁ (x * hs s)) (𝓝 0) (𝓝 (f₁ x)) := fun x => by
    have : Continuous fun s => f₁ (x * hs s) := hf.comp (continuous_const.mul hsc)
    simpa [hs0] using this.tendsto 0
  set J : ℝ → ℝ≥0∞ := fun s => ∫⁻ x, ‖f₁ (x * hs s) - f₁ x‖ₑ ^ 2 ∂ν with hJdef
  suffices hJ : Tendsto J (𝓝 0) (𝓝 0) by
    have h2 : ∀ s, eLpNorm (fun x => f₁ (x * hs s) - f₁ x) 2 ν = J s ^ (1 / 2 : ℝ) := by
      intro s
      rw [eLpNorm_eq_lintegral_rpow_enorm (by norm_num) (by norm_num)]
      simp [J]
    have h3 := ((ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).tendsto 0).comp hJ
    rw [ENNReal.zero_rpow_of_pos (by norm_num)] at h3
    refine h3.congr (fun s => ?_)
    exact (h2 s).symm

  have hBm : ∀ s, Measurable fun x => ‖f₁ (x * hs s) - f₁ x‖ₑ ^ 2 := fun s =>
    ((hf.measurable.comp (measurable_mul_const _)).sub hf.measurable).enorm.pow_const 2
  have hAint : ∀ s, ∫⁻ x, (2 * N (x * hs s) + 2 * N x) ∂ν = 2 * Δ s * I + 2 * I := fun s => by
    rw [lintegral_add_left ((hNm _).const_mul 2), lintegral_const_mul _ (hNm _),
      lintegral_const_mul _ (by simpa using hNm 1), hnorm, mul_assoc]
  have hJle : ∀ s, J s ≤ 2 * Δ s * I + 2 * I := fun s => by
    rw [← hAint]
    exact lintegral_mono fun x => enorm_sub_sq_le _ _
  have hfin : ∀ s, 2 * (Δ s : ℝ≥0∞) * I + 2 * I ≠ ∞ := fun s => by
    simp [ENNReal.mul_eq_top, hI, ENNReal.add_eq_top]
  by_cases hI0 : I = 0
  · have : ∀ s, J s = 0 := fun s => le_antisymm (by simpa [hI0] using hJle s) bot_le
    rw [show J = fun _ => 0 from funext this]
    exact tendsto_const_nhds

  have hfat1 : I ≤ liminf (fun s => (Δ s : ℝ≥0∞) * I) (𝓝 0) := by
    calc I = ∫⁻ x, liminf (fun s => N (x * hs s)) (𝓝 0) ∂ν := by
          refine lintegral_congr fun x => ?_
          exact ((((ENNReal.continuous_pow 2).tendsto _).comp (hpt x).enorm).liminf_eq).symm
      _ ≤ liminf (fun s => ∫⁻ x, N (x * hs s) ∂ν) (𝓝 0) :=
          lintegral_liminf_le fun s => hNm (hs s)
      _ = liminf (fun s => (Δ s : ℝ≥0∞) * I) (𝓝 0) := by simp only [hnorm]
  have hlow : ∀ c : ℝ≥0, c < 1 → ∀ᶠ s in 𝓝 (0 : ℝ), c < Δ s := fun c hc => by
    have h1 : (c : ℝ≥0∞) * I < liminf (fun s => (Δ s : ℝ≥0∞) * I) (𝓝 0) := by
      refine lt_of_lt_of_le ?_ hfat1
      calc (c : ℝ≥0∞) * I < 1 * I :=
            (ENNReal.mul_lt_mul_iff_left hI0 hI).2 (by exact_mod_cast hc)
        _ = I := one_mul _
    filter_upwards [eventually_lt_of_lt_liminf h1] with s hs'
    exact_mod_cast (ENNReal.mul_lt_mul_iff_left hI0 hI).1 hs'
  have hup : ∀ η : ℝ, 0 < η → ∀ᶠ s in 𝓝 (0 : ℝ), (Δ s : ℝ) < 1 + η := fun η hη => by
    set c : ℝ≥0 := Real.toNNReal (1 + η)⁻¹ with hc
    have hcr : (c : ℝ) = (1 + η)⁻¹ := Real.coe_toNNReal _ (by positivity)
    have hc1 : c < 1 := by
      rw [← NNReal.coe_lt_coe, hcr, NNReal.coe_one]
      exact inv_lt_one_of_one_lt₀ (by linarith)
    have hneg : Tendsto (fun s : ℝ => -s) (𝓝 0) (𝓝 0) := by
      simpa using (continuous_neg.tendsto (0 : ℝ))
    filter_upwards [hneg.eventually (hlow c hc1)] with s hs'
    have h1 : (c : ℝ) < Δ (-s) := by exact_mod_cast hs'
    have h2 := hΔneg s
    have hcpos : (0 : ℝ) < c := by rw [hcr]; positivity
    have h3 : (c : ℝ) * (1 + η) = 1 := by rw [hcr]; field_simp
    have hD : (0 : ℝ) ≤ Δ s := NNReal.coe_nonneg _
    nlinarith

  have hN1 : Measurable N := (hf.measurable).enorm.pow_const 2
  have hfat2 : 2 * I + 2 * I ≤
      liminf (fun s => (2 * (Δ s : ℝ≥0∞) * I + 2 * I) - J s) (𝓝 0) := by
    calc 2 * I + 2 * I = ∫⁻ x, (2 * N x + 2 * N x) ∂ν := by
          rw [lintegral_add_left (hN1.const_mul 2), lintegral_const_mul _ hN1]
      _ = ∫⁻ x, liminf (fun s => (2 * N (x * hs s) + 2 * N x)
            - ‖f₁ (x * hs s) - f₁ x‖ₑ ^ 2) (𝓝 0) ∂ν := by
          refine lintegral_congr fun x => ?_
          have hNx : Tendsto (fun s => N (x * hs s)) (𝓝 0) (𝓝 (N x)) :=
            ((ENNReal.continuous_pow 2).tendsto _).comp (hpt x).enorm
          have hA : Tendsto (fun s => 2 * N (x * hs s) + 2 * N x) (𝓝 0)
              (𝓝 (2 * N x + 2 * N x)) :=
            (ENNReal.Tendsto.const_mul hNx (Or.inr ENNReal.ofNat_ne_top)).add tendsto_const_nhds
          have hd : Tendsto (fun s => f₁ (x * hs s) - f₁ x) (𝓝 0) (𝓝 0) := by
            simpa using (hpt x).sub_const (f₁ x)
          have hB : Tendsto (fun s => ‖f₁ (x * hs s) - f₁ x‖ₑ ^ 2) (𝓝 0) (𝓝 0) := by
            have := ((ENNReal.continuous_pow 2).tendsto _).comp hd.enorm
            simpa [Function.comp_def] using this
          have := ENNReal.Tendsto.sub hA hB (Or.inr ENNReal.zero_ne_top)
          rw [tsub_zero] at this
          exact this.liminf_eq.symm
      _ ≤ liminf (fun s => ∫⁻ x, ((2 * N (x * hs s) + 2 * N x)
            - ‖f₁ (x * hs s) - f₁ x‖ₑ ^ 2) ∂ν) (𝓝 0) :=
          lintegral_liminf_le fun s => (((hNm _).const_mul 2).add (hN1.const_mul 2)).sub (hBm s)
      _ = liminf (fun s => (2 * (Δ s : ℝ≥0∞) * I + 2 * I) - J s) (𝓝 0) := by
          congr 1; funext s
          rw [lintegral_sub (hBm s) (ne_top_of_le_ne_top (hfin s) (hJle s))
            (ae_of_all _ fun x => enorm_sub_sq_le _ _), hAint]
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  by_cases hεt : ε = ∞
  · exact Eventually.of_forall fun _ => hεt ▸ le_top
  set e := ε.toReal with he_def
  have he : 0 < e := ENNReal.toReal_pos hε.ne' hεt
  set i := I.toReal with hi_def
  have hi : 0 < i := ENNReal.toReal_pos hI0 hI
  have h4 : ENNReal.ofReal (4 * i - e / 2) < 2 * I + 2 * I := by
    have hne : 2 * I + 2 * I ≠ ∞ := by simp [ENNReal.add_eq_top, ENNReal.mul_eq_top, hI]
    rw [← ENNReal.ofReal_toReal hne, ENNReal.ofReal_lt_ofReal_iff (ENNReal.toReal_pos
      (by simp [hI0]) hne)]
    rw [ENNReal.toReal_add (by simp [ENNReal.mul_eq_top, hI]) (by simp [ENNReal.mul_eq_top, hI]),
      ENNReal.toReal_mul]
    simp only [ENNReal.toReal_ofNat, ← hi_def]
    linarith
  have hv := eventually_lt_of_lt_liminf (lt_of_lt_of_le h4 hfat2)
  filter_upwards [hv, hup (e / (4 * i)) (by positivity)] with s h1 h2
  have hu := hfin s
  have hJs := hJle s
  have hJne : J s ≠ ∞ := ne_top_of_le_ne_top hu hJs
  have hvr := lt_toReal_of_ofReal_lt (ENNReal.sub_ne_top hu) h1
  rw [ENNReal.toReal_sub_of_le hJs hu] at hvr
  have hur : (2 * (Δ s : ℝ≥0∞) * I + 2 * I).toReal = 2 * (Δ s : ℝ) * i + 2 * i := by
    rw [ENNReal.toReal_add (by simp [ENNReal.mul_eq_top, hI]) (by simp [ENNReal.mul_eq_top, hI]),
      ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul]
    simp [← hi_def]
  rw [hur] at hvr
  have key : (Δ s : ℝ) * i < i + e / 4 := by
    have := mul_lt_mul_of_pos_right h2 hi
    have h5 : (1 + e / (4 * i)) * i = i + e / 4 := by field_simp
    linarith
  have hJr : (J s).toReal ≤ e := by linarith
  exact (ENNReal.toReal_le_toReal hJne hεt).1 hJr

end GlobalTheory.RightTranslationL2Continuity
