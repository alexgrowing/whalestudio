import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocalWhittakerDuality.WSteps
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData
open scoped ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.GL2LocalData.WRepNProof

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]
variable {E : Type} [Field E] [TopologicalSpace E] [MeasurableSpace E] [Algebra F E]

theorem nsg_one : nsg E (1 : F) = 1 := by
  unfold nsg
  exact if_pos ⟨1, by simp⟩

theorem rW_n (χ : AddChar F Circle) (σ : E ≃ₐ[F] E) (μ : Measure E) (lam : ℂ) (b : F) (Φ : E → ℂ) :
    rWm χ σ μ lam !![1, b; 0, 1] Φ = fun z => (χ (b * Algebra.norm F z) : ℂ) * Φ z := by
  funext z
  simp [rWm, rW, nsg_one]

theorem rW_mul_n (hfin : Module.finrank F E = 2) (χ : AddChar F Circle) (σ : E ≃ₐ[F] E) (μ : Measure E) (lam : ℂ)
    (g : Matrix (Fin 2) (Fin 2) F) (b : F) (Φ : E → ℂ) :
    rWm χ σ μ lam (g * !![1, b; 0, 1]) Φ = rWm χ σ μ lam g (rWm χ σ μ lam !![1, b; 0, 1] Φ) := by
  rw [rW_n]
  funext z
  have e00 : (g * !![1, b; 0, 1]) 0 0 = g 0 0 := by simp [Matrix.mul_apply, Fin.sum_univ_two]
  have e01 : (g * !![1, b; 0, 1]) 0 1 = g 0 0 * b + g 0 1 := by simp [Matrix.mul_apply, Fin.sum_univ_two]
  have e10 : (g * !![1, b; 0, 1]) 1 0 = g 1 0 := by simp [Matrix.mul_apply, Fin.sum_univ_two]
  have e11 : (g * !![1, b; 0, 1]) 1 1 = g 1 0 * b + g 1 1 := by simp [Matrix.mul_apply, Fin.sum_univ_two]
  simp only [rWm, rW, e00, e01, e10, e11]
  by_cases hc : g 1 0 = 0
  · rw [if_pos (e10.trans hc), if_pos hc]
    have hN : Algebra.norm F (algebraMap F E (g 0 0) * z) = g 0 0 ^ 2 * Algebra.norm F z := by
      rw [map_mul, Algebra.norm_algebraMap, hfin]
    have hadd : g 0 0 * (g 0 0 * b + g 0 1) * Algebra.norm F z =
        g 0 0 * g 0 1 * Algebra.norm F z + b * (g 0 0 ^ 2 * Algebra.norm F z) := by ring
    rw [hN, hadd, AddChar.map_add_eq_mul, Circle.coe_mul]
    ring
  · rw [if_neg (fun h => hc (e10.symm.trans h)), if_neg hc]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    have hadd : (g 0 0 * Algebra.norm F z + (g 1 0 * b + g 1 1) * Algebra.norm F u -
          Algebra.trace F E (σ z * u)) / g 1 0 =
        (g 0 0 * Algebra.norm F z + g 1 1 * Algebra.norm F u - Algebra.trace F E (σ z * u)) / g 1 0 +
          b * Algebra.norm F u := by
      field_simp
      ring
    beta_reduce
    rw [hadd, AddChar.map_add_eq_mul, Circle.coe_mul]
    ring

end GlobalTheory.CompanionTheory.GL2LocalData.WRepNProof

theorem GlobalTheory.CompanionTheory.GL2LocalData.wRepN : Ad3.K.GL2LocalData.WRepN := by
  intro F _ _ _ _ _ _ _ χ _ _ E _ _ _ _ _ _ _ hfin _ σ _ η _ g _ b Φ _
  exact GlobalTheory.CompanionTheory.GL2LocalData.WRepNProof.rW_mul_n hfin χ σ _ _ g b Φ
