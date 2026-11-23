import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FubiniRightConvolutionBoundedContinuousStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqZeroOfAeFundamentalDomainOfLeftInvariantStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousRightConvolutionBoundedIntegrableStatement
open MeasureTheory

namespace GlobalTheory

theorem rightConv_eq_smul_of_inner_translates : ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G) [Countable Γ] (μ : Measure G) [μ.IsHaarMeasure] (𝓕 : Set G), IsFundamentalDomain Γ 𝓕 μ → μ 𝓕 < ⊤ → ∀ {H : Subgroup G} (m : Measure H) [SFinite m] (α : H → ℂ), Integrable α m → ∀ (φ : G → ℂ), Continuous φ → ∀ B : ℝ, (∀ g, ‖φ g‖ ≤ B) → (∀ γ ∈ Γ, ∀ x, φ (γ * x) = φ x) → ∀ c : ℂ, (∀ h' : H, ∫ x in 𝓕, star (φ (x * (h' : G))) * (∫ h, α h * φ (x * (h : G)) ∂m) ∂μ = c * ∫ x in 𝓕, star (φ (x * (h' : G))) * φ x ∂μ) → ∀ x, ∫ h, α h * φ (x * (h : G)) ∂m = c * φ x := by
  intro G _ _ _ _ _ _ Γ _ μ _ 𝓕 hF hμ H m _ α hα φ hφ B hB hinv c hc
  set Φ : G → ℂ := fun x => ∫ h, α h * φ (x * (h : G)) ∂m with hΦdef

  have intOn : ∀ f : G → ℂ, Continuous f → ∀ C : ℝ, (∀ g, ‖f g‖ ≤ C) → IntegrableOn f 𝓕 μ :=
    fun f hf C hC => Measure.integrableOn_of_bounded hμ.ne hf.aestronglyMeasurable (ae_of_all _ hC)
  have hΦc : Continuous Φ := GlobalTheory.T.continuous_right_convolution_bounded_integrable m α hα φ hφ B hB
  set K : ℝ := ∫ h, ‖α h‖ * B ∂m
  have hΦb : ∀ x, ‖Φ x‖ ≤ K := by
    intro x
    refine norm_integral_le_of_norm_le (hα.norm.mul_const B) (ae_of_all _ fun h => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hB _) (norm_nonneg _)
  set D : G → ℂ := fun x => Φ x - c * φ x with hDdef
  have hDc : Continuous D := hΦc.sub (continuous_const.mul hφ)
  have hDb : ∀ x, ‖D x‖ ≤ K + ‖c‖ * B := by
    intro x
    refine (norm_sub_le _ _).trans (add_le_add (hΦb x) ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hB _) (norm_nonneg _)
  have hsφc : Continuous (fun x => star (φ x)) := hφ.star
  have hsφb : ∀ x, ‖star (φ x)‖ ≤ B := fun x => by rw [norm_star]; exact hB x

  have h1 : ∀ h' : H, ∫ x in 𝓕, star (φ (x * (h' : G))) * D x ∂μ = 0 := by
    intro h'
    have hc1 : Continuous (fun x => star (φ (x * (h' : G)))) :=
      hsφc.comp (continuous_id.mul continuous_const)
    have hb1 : ∀ x, ‖star (φ (x * (h' : G)))‖ ≤ B := fun x => hsφb _
    have i1 : IntegrableOn (fun x => star (φ (x * (h' : G))) * Φ x) 𝓕 μ :=
      intOn _ (hc1.mul hΦc) (B * K) fun x => by
        rw [norm_mul]; exact mul_le_mul (hb1 x) (hΦb x) (norm_nonneg _) ((norm_nonneg _).trans (hB 1))
    have i2 : IntegrableOn (fun x => star (φ (x * (h' : G))) * (c * φ x)) 𝓕 μ :=
      intOn _ (hc1.mul (continuous_const.mul hφ)) (B * (‖c‖ * B)) fun x => by
        rw [norm_mul, norm_mul]
        exact mul_le_mul (hb1 x) (mul_le_mul_of_nonneg_left (hB _) (norm_nonneg _)) (by positivity) ((norm_nonneg _).trans (hB 1))
    have : (fun x => star (φ (x * (h' : G))) * D x) = fun x => star (φ (x * (h' : G))) * Φ x - star (φ (x * (h' : G))) * (c * φ x) := by
      funext x; simp only [hDdef]; ring
    rw [this, integral_sub i1 i2, hc h']
    have : (fun x => star (φ (x * (h' : G))) * (c * φ x)) = fun x => c * (star (φ (x * (h' : G))) * φ x) := by
      funext x; ring
    rw [this, integral_const_mul]
    simp [Φ]

  have hsα : Integrable (fun h => star (α h)) m := by
    simpa using Complex.conjCLE.toContinuousLinearMap.integrable_comp hα
  have F := GlobalTheory.T.integral_fundamentalDomain_convolution_comm_of_bounded (H := H) μ 𝓕 hμ m (fun h => star (α h)) hsα D (fun x => star (φ x)) hDc hsφc
    (K + ‖c‖ * B) B hDb hsφb
  have hstarΦ : ∀ x, star (Φ x) = ∫ h, star (α h) * star (φ (x * (h : G))) ∂m := by
    intro x
    simp only [Φ, ← starRingEnd_apply, ← integral_conj, map_mul]
  have h3 : ∫ x in 𝓕, D x * star (Φ x) ∂μ = 0 := by
    simp_rw [hstarΦ]
    rw [F.2.2]
    refine integral_eq_zero_of_ae (ae_of_all _ fun h => ?_)
    have := h1 h
    have e : (fun x => D x * star (φ (x * (h : G)))) = fun x => star (φ (x * (h : G))) * D x := by
      funext x; ring
    simp only [Pi.zero_apply, e, this, mul_zero]

  have h4 : ∫ x in 𝓕, D x * star (φ x) ∂μ = 0 := by
    have := h1 1
    simp only [OneMemClass.coe_one, mul_one] at this
    rw [← this]; congr 1; funext x; ring

  have iDΦ : IntegrableOn (fun x => D x * star (Φ x)) 𝓕 μ :=
    intOn _ (hDc.mul hΦc.star) ((K + ‖c‖ * B) * K) fun x => by
      rw [norm_mul, norm_star]
      exact mul_le_mul (hDb x) (hΦb x) (norm_nonneg _) ((norm_nonneg _).trans (hDb x))
  have iDφ : IntegrableOn (fun x => star c * (D x * star (φ x))) 𝓕 μ :=
    intOn _ (continuous_const.mul (hDc.mul hsφc)) (‖c‖ * ((K + ‖c‖ * B) * B)) fun x => by
      rw [norm_mul, norm_mul, norm_star]
      exact mul_le_mul_of_nonneg_left (mul_le_mul (hDb x) (hsφb x) (norm_nonneg _) ((norm_nonneg _).trans (hDb x))) (norm_nonneg _)
  have h5 : ∫ x in 𝓕, ((‖D x‖ ^ 2 : ℝ) : ℂ) ∂μ = 0 := by
    have e : (fun x => ((‖D x‖ ^ 2 : ℝ) : ℂ)) = fun x => D x * star (Φ x) - star c * (D x * star (φ x)) := by
      funext x
      rw [Complex.ofReal_pow, ← Complex.mul_conj', starRingEnd_apply]
      simp only [hDdef, star_sub, star_mul']
      ring
    rw [e, integral_sub iDΦ iDφ, integral_const_mul, h3, h4, mul_zero, sub_zero]
  rw [integral_complex_ofReal, Complex.ofReal_eq_zero] at h5
  have indexDSecond : IntegrableOn (fun x => ‖D x‖ ^ 2) 𝓕 μ :=
    Measure.integrableOn_of_bounded hμ.ne (hDc.norm.pow 2).aestronglyMeasurable
      (M := (K + ‖c‖ * B) ^ 2) (ae_of_all _ fun x => by
        rw [Real.norm_eq_abs, abs_pow, abs_norm]
        exact pow_le_pow_left₀ (norm_nonneg _) (hDb x) 2)
  have hae := (integral_eq_zero_iff_of_nonneg_ae (ae_of_all _ fun x => by positivity) indexDSecond).1 h5
  have hae' : ∀ᵐ x ∂(μ.restrict 𝓕), D x = 0 := hae.mono fun x hx => by
    simpa using hx

  have hDinv : ∀ γ ∈ Γ, ∀ x, D (γ * x) = D x := by
    intro γ hγ x
    simp only [hDdef, Φ, mul_assoc, hinv γ hγ]
  have := GlobalTheory.T.eq_zero_of_ae_zero_on_fundamentalDomain Γ μ 𝓕 hF D hDc hDinv hae'
  intro x
  exact sub_eq_zero.1 (this x)

end GlobalTheory
