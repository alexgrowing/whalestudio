import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.ConeBDefs
open MeasureTheory FreeSingleHomotopyEquivDiscreteChains.UpperTheory.Dv.ConeB
open scoped FourierTransform SchwartzMap

theorem UpperTheory.schwartz_fourier_preimage :
    ∀ {J : Type} [Fintype J] (β : (J → ℂ) → ℂ), ContDiff ℝ (⊤ : ℕ∞) β → HasCompactSupport β →
        ∃ h : (J → ℂ) → ℂ, Continuous h ∧ (∀ N : ℕ, Integrable fun v => (1 + ‖v‖) ^ N * ‖h v‖) ∧ ∀ x, FT h (-x) = β x := by
  intro J _ β hβ hc
  let e : PiLp 2 (fun _ : J => ℂ) ≃L[ℝ] (J → ℂ) := PiLp.continuousLinearEquiv 2 ℝ _
  let σ : (J → ℂ) ≃L[ℝ] (J → ℂ) := ContinuousLinearEquiv.piCongrRight fun _ => Complex.conjCLE
  let b : 𝓢(J → ℂ, ℂ) := hc.toSchwartzMap hβ
  let g : 𝓢(PiLp 2 (fun _ : J => ℂ), ℂ) := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (e.trans σ) b
  let G : 𝓢(PiLp 2 (fun _ : J => ℂ), ℂ) := 𝓕 g
  let μ : Measure (J → ℂ) := Measure.map e volume
  haveI : μ.IsAddHaarMeasure := e.isAddHaarMeasure_map _
  let c : NNReal := Measure.addHaarScalarFactor μ volume
  have hμ : μ = c • volume := Measure.isAddLeftInvariant_eq_smul _ _
  let H : 𝓢(J → ℂ, ℂ) := ((c : ℝ) : ℂ) • SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e.symm G
  refine ⟨H, H.continuous, fun N => ?_, fun x => ?_⟩
  · simp only [add_comm (1 : ℝ), add_pow, one_pow, mul_one, Finset.sum_mul]
    refine integrable_finsetSum _ fun k _ => ?_
    have := (H.integrable_pow_mul volume k).mul_const (N.choose k : ℝ)
    refine this.congr (Filter.Eventually.of_forall fun v => ?_)
    ring
  · have h1 : FT H (-x) = ∫ s, G (e.symm s) * ec (s * -x) ∂μ := by
      rw [hμ, integral_smul_nnreal_measure, FT, NNReal.smul_def, ← integral_smul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
      simp [H, mul_assoc]
    have h2 : ∫ s, G (e.symm s) * ec (s * -x) ∂μ = ∫ v, G v * ec (e v * -x) := by
      have := integral_map_equiv (μ := volume) e.toHomeomorph.toMeasurableEquiv (fun s => G (e.symm s) * ec (s * -x))
      simpa using this
    have h3 : (𝓕⁻ G : 𝓢(PiLp 2 (fun _ : J => ℂ), ℂ)) = g := FourierTransform.fourierInv_fourier_eq g
    have h4 : g (e.symm (σ x)) = β x := by
      have : σ (σ x) = x := by
        ext j
        simp [σ]
      simp [g, b, this]
    rw [h1, h2, ← h4, ← h3, SchwartzMap.fourierInv_coe, Real.fourierInv_eq']
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    simp only [smul_eq_mul]
    rw [mul_comm, ec]
    congr 2
    simp [PiLp.inner_apply, e, σ, Complex.inner]
    simp only [mul_comm (((v.ofLp _).re : ℝ) : ℂ), mul_comm (((v.ofLp _).im : ℝ) : ℂ)]
    ring
