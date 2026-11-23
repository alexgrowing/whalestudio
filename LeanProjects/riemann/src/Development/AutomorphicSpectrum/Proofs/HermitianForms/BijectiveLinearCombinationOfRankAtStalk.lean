import Mathlib
import Formalism.UnipotentAdelicQuotients.SWXSDefs

open MeasureTheory HeckeCharacterZeroLocus.SiegelWeilU
open scoped FourierTransform RealInnerProductSpace

namespace GlobalTheory.CompanionTheory.SelfDualReal

theorem selfDual_transport {V W : Type} [AddCommGroup V] [TopologicalSpace V] [MeasurableSpace V]
    [BorelSpace V] [AddCommGroup W] [TopologicalSpace W] [IsTopologicalAddGroup W]
    [MeasurableSpace W] [BorelSpace W]
    (f : V ≃+ W) (hf : Continuous f) (hf' : Continuous f.symm) (ν : Measure W) (χ : W → W → ℂ)
    (h : SelfDual ν χ) : SelfDual (ν.map f.symm) (fun x y => χ (f x) (f y)) := by
  let g : W ≃ₜ V := { f.symm.toEquiv with continuous_toFun := hf', continuous_invFun := hf }
  haveI : IsTopologicalAddGroup V := g.symm.isInducing.topologicalAddGroup f.toAddMonoidHom
  obtain ⟨hν, hinv⟩ := h
  have hm : MeasurableEmbedding f.symm := g.measurableEmbedding
  refine ⟨AddEquiv.isAddHaarMeasure_map ν f.symm hf' hf, ?_⟩
  intro Φ hΦ hc hi z
  simp only [hm.integral_map, hm.integrable_map_iff, AddEquiv.apply_symm_apply,
    Function.comp_def] at hi ⊢
  have := hinv (Φ ∘ g) (hΦ.comp g.continuous) (hc.comp_homeomorph g) hi (f z)
  simp only [Function.comp_def] at this
  have h2 : g (-f z) = -z := by
    change f.symm (-f z) = -z
    simp
  rw [h2] at this
  exact this

theorem selfDual_euclid {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    [FiniteDimensional ℝ W] [MeasurableSpace W] [BorelSpace W] (S : W →ₗ[ℝ] W)
    (hS : ∀ x y, ⟪S x, y⟫ = ⟪x, S y⟫) (hd : LinearMap.det S ≠ 0) :
    ∃ ν : Measure W, SelfDual ν
      (fun x y => Complex.exp (((-2 * Real.pi * ⟪x, S y⟫ : ℝ) : ℂ) * Complex.I)) := by
  set d : ℝ := |LinearMap.det S| with hdd
  have hd0 : 0 < d := abs_pos.mpr hd
  set c : ℝ := Real.sqrt d with hc
  have hc0 : 0 < c := Real.sqrt_pos.mpr hd0
  have hcc : c * c = d := Real.mul_self_sqrt hd0.le
  have hne : ENNReal.ofReal c ≠ 0 := by simpa using hc0
  refine ⟨ENNReal.ofReal c • volume,
    Measure.IsAddHaarMeasure.smul volume hne ENNReal.ofReal_ne_top, ?_⟩
  intro Φ hΦ hcs hi z
  have hΦi : Integrable Φ := hΦ.integrable_of_hasCompactSupport hcs
  have hF : ∀ y, ∫ x, Φ x * Complex.exp (((-2 * Real.pi * ⟪x, S y⟫ : ℝ) : ℂ) * Complex.I)
      = 𝓕 Φ (S y) := by
    intro y
    rw [Real.fourier_eq']
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [smul_eq_mul]
    rw [mul_comm]
  let L : W ≃L[ℝ] W := (S.equivOfDetNeZero hd).toContinuousLinearEquiv
  have hm : MeasurableEmbedding S := L.toHomeomorph.measurableEmbedding
  have hmap := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure W) hd
  have hne' : ENNReal.ofReal |(LinearMap.det S)⁻¹| ≠ 0 := by simpa using hd
  simp only [integral_smul_measure, hF, ENNReal.toReal_ofReal hc0.le] at hi ⊢
  rw [integrable_smul_measure hne ENNReal.ofReal_ne_top] at hi
  have hi2 : Integrable (fun y => 𝓕 Φ (S y)) := by
    have := hi.smul c⁻¹
    refine this.congr (Filter.Eventually.of_forall fun y => ?_)
    simp [smul_smul, hc0.ne']
  have hi3 : Integrable (𝓕 Φ) := by
    have h1 : Integrable (𝓕 Φ) (Measure.map S volume) := hm.integrable_map_iff.mpr hi2
    rw [hmap, integrable_smul_measure hne' ENNReal.ofReal_ne_top] at h1
    exact h1
  have hinv := congrFun (hΦ.fourierInv_fourier_eq hΦi hi3) (-z)
  rw [Real.fourierInv_eq_fourier_neg, neg_neg, Real.fourier_eq'] at hinv
  have h3 := hm.integral_map (μ := volume)
    (fun w => Complex.exp (((-2 * Real.pi * ⟪w, z⟫ : ℝ) : ℂ) * Complex.I) • 𝓕 Φ w)
  rw [hmap, integral_smul_measure, hinv, ENNReal.toReal_ofReal (abs_nonneg _), abs_inv,
    ← hdd] at h3
  have h4 : ∫ y, (c • 𝓕 Φ (S y)) * Complex.exp (((-2 * Real.pi * ⟪y, S z⟫ : ℝ) : ℂ) * Complex.I)
      = c • (d⁻¹ • Φ (-z)) := by
    rw [h3, ← integral_smul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [hS, smul_eq_mul, smul_mul_assoc]
    rw [mul_comm]
  rw [h4, smul_smul, smul_smul, hcc, mul_inv_cancel₀ hd0.ne', one_smul]

theorem exists_selfDual : ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [MeasurableSpace V]
    [BorelSpace V] (N : ℕ) (e : V ≃+ (Fin N → ℝ)) (A : Matrix (Fin N) (Fin N) ℝ) (χ : V → V → ℂ),
    Continuous e → Continuous e.symm → A.IsSymm → A.det ≠ 0 →
    (∀ x y, χ x y = Complex.exp (((dotProduct (e x) (A.mulVec (e y)) : ℝ) : ℂ) * Complex.I)) →
    ∃ μ : Measure V, SelfDual μ χ := by
  intro V _ _ _ _ N e A χ he he' hA hd hχ
  let p : EuclideanSpace ℝ (Fin N) ≃L[ℝ] (Fin N → ℝ) := EuclideanSpace.equiv (Fin N) ℝ
  let B : Matrix (Fin N) (Fin N) ℝ := (-2 * Real.pi)⁻¹ • A
  have hpi : (-2 * Real.pi) ≠ 0 := by have := Real.pi_pos; intro h; linarith
  have hB : B.det ≠ 0 := by
    simp only [B, Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero hpi)) hd
  have hBs : B.IsSymm := hA.smul _
  let S : EuclideanSpace ℝ (Fin N) →ₗ[ℝ] EuclideanSpace ℝ (Fin N) :=
    (p.symm.toLinearEquiv : (Fin N → ℝ) →ₗ[ℝ] _) ∘ₗ Matrix.toLin' B ∘ₗ
      (p.symm.toLinearEquiv.symm : _ →ₗ[ℝ] (Fin N → ℝ))
  have hin : ∀ x y : EuclideanSpace ℝ (Fin N), ⟪x, y⟫ = dotProduct (p x) (p y) := by
    intro x y
    rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
    rfl
  have hSa : ∀ y, p (S y) = B.mulVec (p y) := fun y => rfl
  have hS : ∀ x y, ⟪S x, y⟫ = ⟪x, S y⟫ := by
    intro x y
    rw [hin, hin, hSa, hSa, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hBs.eq]
  have hdS : LinearMap.det S ≠ 0 := by
    simp only [S]
    rw [LinearMap.det_conj, LinearMap.det_toLin']
    exact hB
  obtain ⟨ν, hν⟩ := selfDual_euclid S hS hdS
  let f : V ≃+ EuclideanSpace ℝ (Fin N) := e.trans p.symm.toLinearEquiv.toAddEquiv
  have := selfDual_transport f (p.symm.continuous.comp he) (he'.comp p.continuous) ν _ hν
  refine ⟨ν.map f.symm, ?_⟩
  convert this using 3 with x y
  have hpf : ∀ x, p (f x) = e x := fun x => rfl
  rw [hχ, hin, hSa, hpf, hpf]
  simp only [B, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
  rw [mul_inv_cancel_left₀ hpi]

end GlobalTheory.CompanionTheory.SelfDualReal
