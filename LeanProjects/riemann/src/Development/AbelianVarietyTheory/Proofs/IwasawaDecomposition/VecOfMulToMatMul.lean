import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsBlockOrderedSumEquivTrueIndex
open Matrix NumberField MeasureTheory Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.HodgeDomain GlobalTheory.TrueCx GlobalTheory.FlagFibre
open scoped ComplexOrder ENNReal
open scoped Kronecker

namespace GlobalTheory.FlagFibre

theorem vecOf_mul_toMat_mul {p q : ℕ} (R : Matrix (Fin p) (Fin p) ℂ) (T : Matrix (Fin q) (Fin q) ℂ)
    (v : Fin p × Fin q → ℂ) : Formalism.MJ.vecOf (R * toMat v * T) = Matrix.toLin' (R ⊗ₖ Tᵀ) v := by
  funext ⟨a, b⟩
  simp only [Formalism.MJ.vecOf, Matrix.toLin'_apply, mulVec, dotProduct, Fintype.sum_prod_type, Matrix.mul_apply,
    kroneckerMap_apply, transpose_apply, toMat, of_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem lintegral_affine :
    ∀ (p q : ℕ) (R : Matrix (Fin p) (Fin p) ℂ) (T : Matrix (Fin q) (Fin q) ℂ) (C : Matrix (Fin p) (Fin q) ℂ), IsUnit R.det → IsUnit T.det → ∀ f : (Fin p × Fin q → ℂ) → ℝ≥0∞, Measurable f → ∫⁻ v : Fin p × Fin q → ℂ, f (vecOf (R * toMat v * T + C)) = ENNReal.ofReal ((Complex.normSq R.det ^ q * Complex.normSq T.det ^ p)⁻¹) * ∫⁻ v, f v := by
  intro p q R T C hR hT f hf
  set Lr : (Fin p × Fin q → ℂ) →ₗ[ℝ] (Fin p × Fin q → ℂ) := (Matrix.toLin' (R ⊗ₖ Tᵀ)).restrictScalars ℝ with hLr
  have hdet : LinearMap.det Lr = Complex.normSq R.det ^ q * Complex.normSq T.det ^ p := by
    rw [hLr, LinearMap.det_restrictScalars, Algebra.norm_complex_apply, LinearMap.det_toLin', det_kronecker,
      det_transpose]
    simp
  have hpos : 0 < Complex.normSq R.det ^ q * Complex.normSq T.det ^ p :=
    mul_pos (pow_pos (Complex.normSq_pos.2 hR.ne_zero) _) (pow_pos (Complex.normSq_pos.2 hT.ne_zero) _)
  have hdet0 : LinearMap.det Lr ≠ 0 := by rw [hdet]; exact hpos.ne'
  have hLm : Measurable Lr := (LinearMap.continuous_of_finiteDimensional Lr).measurable
  have hg : Measurable fun w : Fin p × Fin q → ℂ => f (w + Formalism.MJ.vecOf C) := hf.comp (measurable_add_const _)
  have e1 : ∫⁻ v : Fin p × Fin q → ℂ, f (Formalism.MJ.vecOf (R * toMat v * T + C)) =
      ∫⁻ w, f (w + Formalism.MJ.vecOf C) ∂(Measure.map Lr volume) := by
    rw [lintegral_map hg hLm]
    refine lintegral_congr fun v => ?_
    have : Formalism.MJ.vecOf (R * toMat v * T + C) = Formalism.MJ.vecOf (R * toMat v * T) + Formalism.MJ.vecOf C := rfl
    rw [this, vecOf_mul_toMat_mul]; rfl
  refine e1.trans ?_
  rw [Measure.map_linearMap_addHaar_eq_smul_addHaar volume hdet0, lintegral_smul_measure, hdet,
    abs_of_nonneg (inv_nonneg.2 hpos.le), smul_eq_mul, lintegral_add_right_eq_self]

end GlobalTheory.FlagFibre
