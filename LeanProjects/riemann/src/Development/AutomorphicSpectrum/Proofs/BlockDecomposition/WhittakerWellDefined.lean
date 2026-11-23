import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.SquareIntegrable.SSmooth
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.SchwartzSpaceL2
open scoped ValuativeRel

namespace GlobalTheory.CompanionTheory.WhittakerTorus

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

theorem integral_comp_unit_mul (ν : Measure F) [ν.IsAddHaarMeasure] (h : Fˣ) (G : F → ℂ) :
    ∫ y, G ((h : F) * y) ∂ν = ((modulus (h : F) : ℝ) : ℂ)⁻¹ * ∫ t, G t ∂ν := by
  have hne : (h : F) ≠ 0 := h.ne_zero
  have hemb : MeasurableEmbedding (fun x : F => (h : F) * x) :=
    (Homeomorph.mulLeft₀ (h : F) hne).measurableEmbedding
  have h1 : ∫ t, G t ∂(Measure.map (fun x : F => (h : F) * x) ν) = ∫ y, G ((h : F) * y) ∂ν :=
    hemb.integral_map G
  rw [← h1, map_mul_left_eq_smul ν hne, integral_smul_nnreal_measure]
  simp [NNReal.smul_def]

theorem mp_one (h : Fˣ) : mp h 1 = ((modulus (h : F) : ℝ) : ℂ) := by
  simp [mp]

theorem det_diagonal_two (a : Fˣ) : GeneralLinearGroup.det (dg2 a (1 : Fˣ)) = a := by
  ext
  simp [dg2, Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]

theorem vecMul_diagonal_bottom_row (a : Fˣ) (u v : F) :
    ![u, v] ᵥ* ((dg2 a (1 : Fˣ) : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = ![u * a, v] := by
  ext i
  fin_cases i <;> simp [dg2, Matrix.vecMul, dotProduct, Fin.sum_univ_two]

theorem inner_pt (ψ : AddChar F Circle) (f g : F → ℂ) (a h : Fˣ) :
    mp h 1 * ∫ x, pt f g (![(h : F), h * x] ᵥ* ((dg2 a (1 : Fˣ) : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) *
        (ψ (-x) : ℂ) ∂selfDualMeasure ψ =
      f ((h : F) * a) * localFourier (selfDualMeasure ψ) ψ g (-((h⁻¹ : Fˣ) : F)) := by
  have hne : (h : F) ≠ 0 := h.ne_zero
  have hm : ((modulus (h : F) : ℝ) : ℂ) ≠ 0 := by
    have := modulus_ne_zero hne
    exact_mod_cast this
  have e1 : ∀ x : F, pt f g (![(h : F), h * x] ᵥ* ((dg2 a (1 : Fˣ) : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) *
        (ψ (-x) : ℂ) = f ((h : F) * a) *
          ((fun t : F => g t * (ψ (t * (-((h⁻¹ : Fˣ) : F))) : ℂ)) ((h : F) * x)) := by
    intro x
    have e2 : ((h : F) * x) * (-((h⁻¹ : Fˣ) : F)) = -x := by
      rw [Units.val_inv_eq_inv_val]
      field_simp
    simp only [vecMul_diagonal_bottom_row, pt, e2]
    simp [mul_assoc]
  have e3 := integral_comp_unit_mul (selfDualMeasure ψ) h
    (fun t : F => g t * (ψ (t * (-((h⁻¹ : Fˣ) : F))) : ℂ))
  rw [integral_congr_ae (Filter.Eventually.of_forall e1), integral_const_mul, e3, mp_one]
  unfold localFourier
  rw [mul_left_comm, mul_inv_cancel_left₀ hm]

theorem swd : SWd := by
  intro F _ _ _ _ _ _ ψ _ μ₁ μ₂ _ _ f _ g _ a
  unfold W2
  rw [det_diagonal_two]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun h => ?_)
  have := inner_pt ψ f g a h
  simp only [mul_assoc] at this ⊢
  rw [this]

end GlobalTheory.CompanionTheory.WhittakerTorus
