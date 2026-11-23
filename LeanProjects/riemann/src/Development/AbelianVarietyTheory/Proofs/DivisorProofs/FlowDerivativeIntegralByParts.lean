import Mathlib
open MeasureTheory Filter Topology
open scoped ENNReal

namespace GlobalTheory

theorem sq_lintegral_le_measure_univ_mul_lintegral_sq {X : Type} [MeasurableSpace X] (ν : Measure X)
    {h : X → ℝ≥0∞} (hh : AEMeasurable h ν) :
    (∫⁻ y, h y ∂ν) ^ 2 ≤ ν Set.univ * ∫⁻ y, h y ^ 2 ∂ν := by
  have H := ENNReal.lintegral_mul_le_Lp_mul_Lq ν Real.HolderConjugate.two_two
    (f := fun _ => 1) (g := h) aemeasurable_const hh
  simp only [Pi.mul_apply, one_mul, ENNReal.one_rpow, lintegral_const, one_mul, ENNReal.rpow_two] at H
  have e2 : ∀ a : ℝ≥0∞, (a ^ (1 / 2 : ℝ)) ^ 2 = a := fun a => by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; norm_num
  refine (pow_le_pow_left' H 2).trans (le_of_eq ?_)
  rw [mul_pow, e2, e2, one_pow, one_mul]

theorem eLpNorm_diffQuot_sub_deriv_le_iSup {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [LocallyCompactSpace H] [SecondCountableTopology H] [T2Space H] [MeasurableSpace H] [BorelSpace H]
    (μ : Measure H) [μ.IsHaarMeasure] (𝓕 : Set H) (γ : Multiplicative ℝ →* H) (hγ : Continuous γ)
    (f f₁ : H → ℂ) (hder : ∀ x, HasDerivAt (fun t : ℝ => f (x * γ (Multiplicative.ofAdd t))) (f₁ x) 0)
    (hf₁ : Continuous f₁) (t : ℝ) (ht : t ≠ 0) :
    eLpNorm (fun x => (t : ℂ)⁻¹ * (f (x * γ (Multiplicative.ofAdd t)) - f x) - f₁ x) 2 (μ.restrict 𝓕) ≤
      ⨆ s ∈ Set.uIcc 0 t, eLpNorm (fun x => f₁ (x * γ (Multiplicative.ofAdd s)) - f₁ x) 2 (μ.restrict 𝓕) := by
  set g : H → ℝ → ℂ := fun x s => f₁ (x * γ (Multiplicative.ofAdd s)) - f₁ x with hg
  set S := ⨆ s ∈ Set.uIcc 0 t, eLpNorm (fun x => f₁ (x * γ (Multiplicative.ofAdd s)) - f₁ x) 2 (μ.restrict 𝓕)
  have hγc : Continuous fun s : ℝ => γ (Multiplicative.ofAdd s) := hγ.comp continuous_ofAdd
  have hgc : Continuous fun p : H × ℝ => g p.1 p.2 := by
    simp only [hg]
    exact (hf₁.comp (continuous_fst.mul (hγc.comp continuous_snd))).sub (hf₁.comp continuous_fst)

  have hftc : ∀ x, ∫ s in (0:ℝ)..t, f₁ (x * γ (Multiplicative.ofAdd s)) =
      f (x * γ (Multiplicative.ofAdd t)) - f x := by
    intro x
    have hd : ∀ s : ℝ, HasDerivAt (fun u : ℝ => f (x * γ (Multiplicative.ofAdd u)))
        (f₁ (x * γ (Multiplicative.ofAdd s))) s := by
      intro s
      have h0 := hder (x * γ (Multiplicative.ofAdd s))
      rw [← sub_self s] at h0
      have h2 : HasDerivAt (fun u : ℝ => u - s) 1 s := (hasDerivAt_id' s).sub_const s
      have h1 := HasDerivAt.scomp (h := fun u : ℝ => u - s) s h0 h2
      rw [one_smul] at h1
      have heq : (fun u : ℝ => f (x * γ (Multiplicative.ofAdd u))) =
          (fun t => f (x * γ (Multiplicative.ofAdd s) * γ (Multiplicative.ofAdd t))) ∘ fun u : ℝ => u - s := by
        funext u
        simp only [Function.comp_apply]
        rw [mul_assoc, ← map_mul, ← ofAdd_add, add_sub_cancel]
      rw [heq]
      exact h1
    have hc : Continuous fun s : ℝ => f₁ (x * γ (Multiplicative.ofAdd s)) :=
      hf₁.comp (continuous_const.mul hγc)
    have := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd s) (hc.intervalIntegrable 0 t)
    simpa using this
  have hF : ∀ x, (t : ℂ)⁻¹ * (f (x * γ (Multiplicative.ofAdd t)) - f x) - f₁ x =
      (t : ℂ)⁻¹ * ∫ s in (0:ℝ)..t, g x s := by
    intro x
    have hc : Continuous fun s : ℝ => f₁ (x * γ (Multiplicative.ofAdd s)) :=
      hf₁.comp (continuous_const.mul hγc)
    simp only [hg]
    rw [intervalIntegral.integral_sub (hc.intervalIntegrable 0 t) intervalIntegrable_const, hftc,
      intervalIntegral.integral_const, Complex.real_smul]
    have : (t : ℂ) ≠ 0 := by exact_mod_cast ht
    push_cast
    field_simp
    ring

  have hL : ∀ (ν : Measure H) (F : H → ℂ), eLpNorm F 2 ν ^ 2 = ∫⁻ x, ‖F x‖ₑ ^ 2 ∂ν := by
    intro ν F
    have := eLpNorm_nnreal_pow_eq_lintegral (μ := ν) (f := F) (p := 2) two_ne_zero
    simpa [ENNReal.rpow_two] using this
  have htn0 : ‖t‖ₑ ≠ 0 := by simpa using ht
  have htnt : ‖t‖ₑ ≠ ∞ := enorm_ne_top
  have hvol : volume (Set.uIoc 0 t) = ‖t‖ₑ := by
    rw [Real.volume_uIoc, sub_zero, Real.enorm_eq_ofReal_abs]

  have hpt : ∀ x, ‖(t : ℂ)⁻¹ * ∫ s in (0:ℝ)..t, g x s‖ₑ ^ 2 ≤
      ‖t‖ₑ⁻¹ * ∫⁻ s in Set.uIoc 0 t, ‖g x s‖ₑ ^ 2 := by
    intro x
    have hgx : Continuous fun s => g x s := hgc.comp (continuous_const.prodMk continuous_id)
    have h1 : ‖∫ s in (0:ℝ)..t, g x s‖ₑ ≤ ∫⁻ s in Set.uIoc 0 t, ‖g x s‖ₑ := by
      have := intervalIntegral.norm_integral_eq_norm_integral_uIoc (μ := volume) (a := 0) (b := t) (fun s => g x s)
      rw [← enorm_norm, this, enorm_norm]
      exact enorm_integral_le_lintegral_enorm _
    have h2 := sq_lintegral_le_measure_univ_mul_lintegral_sq (volume.restrict (Set.uIoc 0 t))
      (hgx.measurable.enorm.aemeasurable)
    rw [Measure.restrict_apply_univ, hvol] at h2
    have hinv : ‖((t : ℂ))⁻¹‖ₑ = ‖t‖ₑ⁻¹ := by
      rw [enorm_inv (by exact_mod_cast ht)]
      congr 1
      simp [← ofReal_norm_eq_enorm]
    rw [enorm_mul, hinv, mul_pow]
    calc ‖t‖ₑ⁻¹ ^ 2 * ‖∫ s in (0:ℝ)..t, g x s‖ₑ ^ 2
        ≤ ‖t‖ₑ⁻¹ ^ 2 * (‖t‖ₑ * ∫⁻ s in Set.uIoc 0 t, ‖g x s‖ₑ ^ 2) := by
          gcongr
          exact (pow_le_pow_left' h1 2).trans h2
      _ = ‖t‖ₑ⁻¹ * ∫⁻ s in Set.uIoc 0 t, ‖g x s‖ₑ ^ 2 := by
          rw [sq, ← mul_assoc, mul_assoc _ _ ‖t‖ₑ, ENNReal.inv_mul_cancel htn0 htnt, mul_one]

  have hmeas : Measurable fun p : H × ℝ => ‖g p.1 p.2‖ₑ ^ 2 := hgc.measurable.enorm.pow_const 2
  have hinner : ∀ s ∈ Set.uIoc 0 t, ∫⁻ x in 𝓕, ‖g x s‖ₑ ^ 2 ∂μ ≤ S ^ 2 := by
    intro s hs
    rw [← hL]
    gcongr
    exact le_iSup₂ (f := fun s _ => eLpNorm (fun x => f₁ (x * γ (Multiplicative.ofAdd s)) - f₁ x) 2
      (μ.restrict 𝓕)) s (Set.uIoc_subset_uIcc hs)
  have key : eLpNorm (fun x => (t : ℂ)⁻¹ * (f (x * γ (Multiplicative.ofAdd t)) - f x) - f₁ x) 2
      (μ.restrict 𝓕) ^ 2 ≤ S ^ 2 := by
    rw [hL]
    calc ∫⁻ x in 𝓕, ‖(t : ℂ)⁻¹ * (f (x * γ (Multiplicative.ofAdd t)) - f x) - f₁ x‖ₑ ^ 2 ∂μ
        ≤ ∫⁻ x in 𝓕, (‖t‖ₑ⁻¹ * ∫⁻ s in Set.uIoc 0 t, ‖g x s‖ₑ ^ 2) ∂μ := by
          refine lintegral_mono fun x => ?_
          rw [hF x]
          exact hpt x
      _ = ‖t‖ₑ⁻¹ * ∫⁻ s in Set.uIoc 0 t, ∫⁻ x in 𝓕, ‖g x s‖ₑ ^ 2 ∂μ := by
          rw [lintegral_const_mul' _ _ (ENNReal.inv_ne_top.mpr htn0)]
          congr 1
          exact lintegral_lintegral_swap (μ := μ.restrict 𝓕) (ν := volume.restrict (Set.uIoc 0 t))
            (f := fun x s => ‖g x s‖ₑ ^ 2) hmeas.aemeasurable
      _ ≤ ‖t‖ₑ⁻¹ * ∫⁻ s in Set.uIoc 0 t, S ^ 2 := by
          exact mul_le_mul' le_rfl (setLIntegral_mono measurable_const hinner)
      _ = S ^ 2 := by
          rw [setLIntegral_const, hvol, ← mul_assoc, mul_comm, ← mul_assoc, ENNReal.mul_inv_cancel htn0 htnt,
            one_mul]
  exact (ENNReal.pow_le_pow_left_iff two_ne_zero).mp key

end GlobalTheory
