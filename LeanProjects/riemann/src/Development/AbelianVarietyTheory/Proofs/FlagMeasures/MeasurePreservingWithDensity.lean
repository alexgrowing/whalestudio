import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SigmaFiniteOfRealSmul
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LinearIndependentSkew

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso

namespace GlobalTheory.HaarMul

theorem measurePreserving_withDensity {X : Type} [MeasurableSpace X] (μ : Measure X) {f : X → X}
    (hf : Measurable f) {ρ : X → ENNReal} (hρ : Measurable ρ) {c d : ENNReal} (hcd : d * c = 1)
    (hμ : μ.map f = c • μ) (hρf : ∀ x, ρ x = d * ρ (f x)) :
    MeasurePreserving f (μ.withDensity ρ) (μ.withDensity ρ) := by
  refine ⟨hf, ?_⟩
  ext s hs
  rw [Measure.map_apply hf hs, withDensity_apply _ (hf hs), withDensity_apply _ hs]

  have h1 : ∫⁻ x in f ⁻¹' s, ρ x ∂μ = ∫⁻ x, d * s.indicator ρ (f x) ∂μ := by
    rw [← lintegral_indicator (hf hs)]
    congr 1
    funext x
    by_cases hx : f x ∈ s
    · simp [Set.indicator_apply, hx, ← hρf x]
    · simp [Set.indicator_apply, hx]
  rw [h1, lintegral_const_mul d (f := fun x => s.indicator ρ (f x)) ((hρ.indicator hs).comp hf),
    ← lintegral_map (hρ.indicator hs) hf, hμ,
    lintegral_smul_measure, smul_eq_mul, ← mul_assoc, hcd, one_mul, lintegral_indicator hs]

theorem measurePreserving_mul_mul : ∀ (j : ℕ) (a b : Matrix (Fin j) (Fin j) ℂ), a.det ≠ 0 → b.det ≠ 0 →
    MeasurePreserving (fun (x : Fin j → Fin j → ℂ) (r s : Fin j) => (a * Matrix.of x * b) r s)
      (haarLoc j) (haarLoc j) := by
  intro j a b ha hb

  let L : (Fin j → Fin j → ℂ) →ₗ[ℝ] (Fin j → Fin j → ℂ) :=
    { toFun := fun x r s => (a * Matrix.of x * b) r s
      map_add' := fun x y => by
        have h : a * Matrix.of (x + y) * b = a * Matrix.of x * b + a * Matrix.of y * b := by
          rw [show Matrix.of (x + y) = Matrix.of x + Matrix.of y from rfl, Matrix.mul_add, Matrix.add_mul]
        funext r s
        exact congrFun (congrFun h r) s
      map_smul' := fun c x => by
        have h : a * Matrix.of (c • x) * b = c • (a * Matrix.of x * b) := by
          rw [show Matrix.of (c • x) = c • Matrix.of x from rfl, Matrix.mul_smul, Matrix.smul_mul]
        funext r s
        exact congrFun (congrFun h r) s }
  have hdet : LinearMap.det L = ‖a.det‖ ^ (2 * j) * ‖b.det‖ ^ (2 * j) :=
    GlobalTheory.TwoSidedJac.real_jacobians.1 j j a b L (fun T => rfl)
  have hA : ‖a.det‖ ≠ 0 := norm_ne_zero_iff.2 ha
  have hB : ‖b.det‖ ≠ 0 := norm_ne_zero_iff.2 hb
  have hD : 0 < ‖a.det‖ ^ (2 * j) * ‖b.det‖ ^ (2 * j) :=
    mul_pos (pow_pos (norm_pos_iff.2 ha) _) (pow_pos (norm_pos_iff.2 hb) _)
  have hcont : Continuous fun x : Fin j → Fin j → ℂ => (Matrix.of x).det :=
    (continuous_id.matrix_det : Continuous fun A : Matrix (Fin j) (Fin j) ℂ => A.det)
  have hρ : Measurable fun x : Fin j → Fin j → ℂ => ENNReal.ofReal ((‖(Matrix.of x).det‖ ^ 2)⁻¹ ^ j) :=
    ENNReal.measurable_ofReal.comp (((hcont.measurable.norm.pow_const 2).inv).pow_const j)

  haveI : (volume : Measure ℂ).IsAddHaarMeasure := inferInstance
  haveI : (volume : Measure (Fin j → ℂ)).IsAddHaarMeasure :=
    Measure.pi.isAddHaarMeasure (fun _ : Fin j => (volume : Measure ℂ))
  haveI : (volume : Measure (Fin j → Fin j → ℂ)).IsAddHaarMeasure :=
    Measure.pi.isAddHaarMeasure (fun _ : Fin j => (volume : Measure (Fin j → ℂ)))
  have hμ : (volume : Measure (Fin j → Fin j → ℂ)).map L =
      ENNReal.ofReal |(LinearMap.det L)⁻¹| • volume :=
    Measure.map_linearMap_addHaar_eq_smul_addHaar _ (by rw [hdet]; exact hD.ne')
  have hcd : ENNReal.ofReal (‖a.det‖ ^ (2 * j) * ‖b.det‖ ^ (2 * j)) * ENNReal.ofReal |(LinearMap.det L)⁻¹| = 1 := by
    rw [hdet, abs_of_pos (inv_pos.2 hD), ← ENNReal.ofReal_mul hD.le, mul_inv_cancel₀ hD.ne', ENNReal.ofReal_one]

  have hρf : ∀ x : Fin j → Fin j → ℂ, ENNReal.ofReal ((‖(Matrix.of x).det‖ ^ 2)⁻¹ ^ j) =
      ENNReal.ofReal (‖a.det‖ ^ (2 * j) * ‖b.det‖ ^ (2 * j)) *
        ENNReal.ofReal ((‖(Matrix.of (L x)).det‖ ^ 2)⁻¹ ^ j) := by
    intro x
    rw [← ENNReal.ofReal_mul hD.le]
    congr 1
    rw [show Matrix.of (L x) = a * Matrix.of x * b from rfl, Matrix.det_mul, Matrix.det_mul, norm_mul, norm_mul]
    have hP : (‖a.det‖ ^ 2) ^ j * ((‖a.det‖ ^ 2) ^ j)⁻¹ = 1 := mul_inv_cancel₀ (pow_ne_zero _ (pow_ne_zero _ hA))
    have hQ : (‖b.det‖ ^ 2) ^ j * ((‖b.det‖ ^ 2) ^ j)⁻¹ = 1 := mul_inv_cancel₀ (pow_ne_zero _ (pow_ne_zero _ hB))
    rw [mul_pow, mul_pow, mul_inv, mul_inv, mul_pow, mul_pow, inv_pow (‖a.det‖ ^ 2), inv_pow (‖b.det‖ ^ 2),
      pow_mul, pow_mul]
    linear_combination (-((‖(Matrix.of x).det‖ ^ 2)⁻¹ ^ j * (‖b.det‖ ^ 2) ^ j * ((‖b.det‖ ^ 2) ^ j)⁻¹)) * hP
      - (‖(Matrix.of x).det‖ ^ 2)⁻¹ ^ j * hQ
  unfold haarLoc
  exact measurePreserving_withDensity volume L.continuous_of_finiteDimensional.measurable hρ hcd hμ hρf

end GlobalTheory.HaarMul
