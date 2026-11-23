import Mathlib
open MeasureTheory FourierTransform

namespace GlobalTheory

open MeasureTheory FourierTransform in

theorem _root_.GlobalTheory.exists_pos_integral_comp_equiv_haar {V E : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (T : V ≃L[ℝ] E) (μ : Measure V) [μ.IsAddHaarMeasure] :
    ∃ a : ℝ, 0 < a ∧ (∀ g : E → ℂ, ∫ x, g (T x) ∂μ = (a : ℂ) * ∫ w, g w) ∧
      ∀ g : E → ℂ, Integrable (fun x => g (T x)) μ ↔ Integrable g := by
  let e : V ≃ᵐ E := T.toHomeomorph.toMeasurableEquiv
  have : (μ.map e).IsAddHaarMeasure := T.isAddHaarMeasure_map μ
  set c := (μ.map e).addHaarScalarFactor volume
  have hpos : 0 < c := Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _
  have hmap : μ.map e = c • volume := Measure.isAddLeftInvariant_eq_smul _ _
  refine ⟨c, hpos, fun g => ?_, fun g => ?_⟩
  · change ∫ x, g (e x) ∂μ = _
    rw [← integral_map_equiv e, hmap, integral_smul_nnreal_measure]
    simp [NNReal.smul_def, Complex.real_smul]
  · change Integrable (g ∘ e) μ ↔ _
    rw [← integrable_map_equiv e, hmap,
      show c • (volume : Measure E) = (c : ENNReal) • volume from rfl, integrable_smul_measure]
    · simpa using hpos.ne'
    · simp

open MeasureTheory FourierTransform in

theorem _root_.GlobalTheory.exists_equiv_inner_eq_form {V E : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (T : V ≃L[ℝ] E) (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hs : ∀ x y, B x y = B y x) (hn : ∀ x, (∀ y, B x y = 0) → x = 0) :
    ∃ R : V ≃L[ℝ] E, ∀ x y, B x y = inner ℝ (T x) (R y) := by
  let φ : V → StrongDual ℝ E := fun y =>
    LinearMap.toContinuousLinearMap ((B.flip y).comp (T.symm : E →L[ℝ] V).toLinearMap)
  have hφ : ∀ y e, φ y e = B (T.symm e) y := fun _ _ => rfl
  let L : V →ₗ[ℝ] E :=
    { toFun := fun y => (InnerProductSpace.toDual ℝ E).symm (φ y)
      map_add' := fun y z => by
        apply (InnerProductSpace.toDual ℝ E).injective
        ext e
        simp [hφ]
      map_smul' := fun r y => by
        apply (InnerProductSpace.toDual ℝ E).injective
        ext e
        simp [hφ] }
  have hL : ∀ x y, inner ℝ (T x) (L y) = B x y := by
    intro x y
    rw [real_inner_comm]
    change inner ℝ ((InnerProductSpace.toDual ℝ E).symm (φ y)) (T x) = _
    rw [InnerProductSpace.toDual_symm_apply, hφ, T.symm_apply_apply]
  have hinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    apply hn y
    intro x
    rw [hs, ← hL, hy, inner_zero_right]
  have hdim : Module.finrank ℝ V = Module.finrank ℝ E := T.toLinearEquiv.finrank_eq
  refine ⟨(LinearMap.linearEquivOfInjective L hinj hdim).toContinuousLinearEquiv, fun x y => ?_⟩
  rw [← hL]
  rfl

open MeasureTheory FourierTransform in

theorem _root_.GlobalTheory.fourier_inversion_haar_symm_form :
    ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ), (∀ x y, B x y = B y x) → (∀ x, (∀ y, B x y = 0) → x = 0) → ∀ μ : Measure V, μ.IsAddHaarMeasure → (∃ c : ℝ, 0 < c ∧ ∀ Φ : V → ℂ, Continuous Φ → Integrable Φ μ → Integrable (fun y => ∫ x, Φ x * Complex.exp (2 * Real.pi * Complex.I * ((B x y : ℝ) : ℂ)) ∂μ) μ → ∀ z, ∫ y, (∫ x, Φ x * Complex.exp (2 * Real.pi * Complex.I * ((B x y : ℝ) : ℂ)) ∂μ) * Complex.exp (2 * Real.pi * Complex.I * ((B y z : ℝ) : ℂ)) ∂μ = (c : ℂ) * Φ (-z)) ∧ ∀ Φ : SchwartzMap V ℂ, Integrable (⇑Φ) μ ∧ Integrable (fun y => ∫ x, Φ x * Complex.exp (2 * Real.pi * Complex.I * ((B x y : ℝ) : ℂ)) ∂μ) μ := by
  intro V _ _ _ _ _ B hs hn μ hμ
  let E := EuclideanSpace ℝ (Fin (Module.finrank ℝ V))
  let T : V ≃L[ℝ] E := (LinearEquiv.ofFinrankEq V E (by simp [E])).toContinuousLinearEquiv
  obtain ⟨R, hR⟩ := _root_.GlobalTheory.exists_equiv_inner_eq_form T B hs hn
  obtain ⟨a, ha, hint, hintg⟩ := _root_.GlobalTheory.exists_pos_integral_comp_equiv_haar T μ
  obtain ⟨b, hb, hint', hintg'⟩ := _root_.GlobalTheory.exists_pos_integral_comp_equiv_haar R μ
  have hF : ∀ (g : E → ℂ) w, 𝓕⁻ g w =
      ∫ v, g v * Complex.exp (2 * Real.pi * Complex.I * ((inner ℝ v w : ℝ) : ℂ)) := by
    intro g w
    rw [Real.fourierInv_eq']
    congr 1
    ext v
    rw [smul_eq_mul, mul_comm]
    congr 2
    push_cast
    ring
  have key : ∀ (Φ : V → ℂ) y, ∫ x, Φ x * Complex.exp (2 * Real.pi * Complex.I * ((B x y : ℝ) : ℂ)) ∂μ
      = a * 𝓕⁻ (fun w => Φ (T.symm w)) (R y) := by
    intro Φ y
    rw [hF, ← hint]
    simp only [hR, ContinuousLinearEquiv.symm_apply_apply]
  have hFF : ∀ g : E → ℂ, Continuous g → Integrable g → Integrable (𝓕⁻ g) → ∀ w,
      𝓕⁻ (𝓕⁻ g) w = g (-w) := by
    intro g hc hg hg' w
    have h1 : 𝓕 g = fun w => 𝓕⁻ g (-w) := by
      ext w
      rw [Real.fourierInv_eq_fourier_neg, neg_neg]
    have h2 : Integrable (𝓕 g) := by
      rw [h1]
      exact hg'.comp_neg
    rw [Real.fourierInv_eq_fourier_neg, hc.fourier_fourierInv_eq hg h2]
  refine ⟨⟨a * b, mul_pos ha hb, fun Φ hc hΦ hI z => ?_⟩, fun Φ => ?_⟩
  · set g : E → ℂ := fun w => Φ (T.symm w) with hg
    have hgc : Continuous g := hc.comp T.symm.continuous
    have hgi : Integrable g := by
      rw [← hintg]
      simpa [g] using hΦ
    have hgi' : Integrable (𝓕⁻ g) := by
      rw [← hintg']
      have := hI.const_mul ((a : ℂ)⁻¹)
      refine this.congr (Filter.Eventually.of_forall fun y => ?_)
      dsimp only
      rw [key, ← hg, ← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast ha.ne'), one_mul]
    simp only [key Φ, ← hg]
    have hB : ∀ y, B y z = inner ℝ (R y) (T z) := fun y => by rw [hs, hR, real_inner_comm]
    simp only [hB]
    rw [hint' (fun u => (a : ℂ) * 𝓕⁻ g u * Complex.exp (2 * Real.pi * Complex.I * ((inner ℝ u (T z) : ℝ) : ℂ)))]
    simp only [mul_assoc (a : ℂ)]
    rw [integral_const_mul, ← hF, hFF g hgc hgi hgi', hg]
    beta_reduce
    rw [← map_neg T z, ContinuousLinearEquiv.symm_apply_apply]
    push_cast
    ring
  · refine ⟨Φ.integrable, ?_⟩
    let ψ := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ T.symm Φ
    have hψ : (fun w => Φ (T.symm w)) = ⇑ψ := by
      ext w
      simp [ψ]
    simp only [key, hψ, ← SchwartzMap.fourierInv_coe]
    refine Integrable.const_mul ?_ _
    rw [hintg' (⇑(𝓕⁻ ψ : SchwartzMap E ℂ))]
    exact (𝓕⁻ ψ : SchwartzMap E ℂ).integrable

end GlobalTheory
