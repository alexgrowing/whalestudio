import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.CasselmanShalikaStandardVector
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BndIUnits
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrablePowerWeightUnits
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ValMeasurableEmbedding
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open Ad3.R (G2 Jd md KA lc)
open scoped NumberField.AdeleRing ValuativeRel
open GlobalTheory.CompanionTheory.GL2Factorization

namespace GlobalTheory.CompanionTheory.GL2Factorization.IwasawaDual

theorem tinvR_mul {n : Type} [Fintype n] [DecidableEq n] (g h : GL n ℝ) :
    GL2LocalData.tinvR (g * h) = GL2LocalData.tinvR g * GL2LocalData.tinvR h := by
  apply Units.ext
  simp [GL2LocalData.tinvR, Matrix.transpose_mul]

theorem tinvR_orth (k : GL (Fin 2) ℝ) (hk : k.val * k.valᵀ = 1) : GL2LocalData.tinvR k = k := by
  have h1 : k.val * (k⁻¹ : GL (Fin 2) ℝ).val = 1 := by
    rw [← Units.val_mul]; simp
  have h2 : (k⁻¹ : GL (Fin 2) ℝ).val = k.valᵀ := by
    have h3 : (k⁻¹ : GL (Fin 2) ℝ).val * k.val = 1 := by
      rw [← Units.val_mul]; simp
    calc (k⁻¹ : GL (Fin 2) ℝ).val = (k⁻¹ : GL (Fin 2) ℝ).val * (k.val * k.valᵀ) := by rw [hk, mul_one]
      _ = k.valᵀ := by rw [← mul_assoc, h3, one_mul]
  apply Units.ext
  show (k⁻¹ : GL (Fin 2) ℝ).valᵀ = k.val
  rw [h2, Matrix.transpose_transpose]

theorem transposeInv_diagonal_real (x y : ℝˣ) : GL2LocalData.tinvR (dg2 x y) = dg2 x⁻¹ y⁻¹ := by
  have h : (dg2 x y)⁻¹ = dg2 x⁻¹ y⁻¹ := by
    rw [inv_eq_iff_mul_eq_one]
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [dg2, Matrix.mul_apply, Fin.sum_univ_two]
  apply Units.ext
  show ((dg2 x y)⁻¹ : GL (Fin 2) ℝ).valᵀ = _
  rw [h]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dg2]

theorem weyl_mul_diagonal_real (x y : ℝˣ) : GL2LocalData.w2R * dg2 x y = dg2 y x * GL2LocalData.w2R := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dg2, GL2LocalData.w2R, Matrix.mul_apply, Fin.sum_univ_two]

theorem weyl_real_orthogonal : GL2LocalData.w2R.val * GL2LocalData.w2R.valᵀ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [GL2LocalData.w2R, Matrix.mul_apply, Fin.sum_univ_two]

theorem iwasawa_dual : ∀ (a b : ℝˣ) (k : GL (Fin 2) ℝ), k.val * k.valᵀ = 1 → ∃ k' : GL (Fin 2) ℝ, k'.val * k'.valᵀ = 1 ∧ GL2LocalData.w2R * GL2LocalData.tinvR (dg2 (a * b) b * k) = dg2 (a * (a * b)⁻¹) (a * b)⁻¹ * k' := by
  intro a b k hk
  refine ⟨GL2LocalData.w2R * k, ?_, ?_⟩
  · have : (GL2LocalData.w2R * k).val = GL2LocalData.w2R.val * k.val := rfl
    rw [this, Matrix.transpose_mul, mul_assoc, ← mul_assoc k.val, hk, one_mul, weyl_real_orthogonal]
  · have hab : a * (a * b)⁻¹ = b⁻¹ := by
      rw [mul_inv, ← mul_assoc, mul_inv_cancel, one_mul]
    rw [tinvR_mul, tinvR_orth k hk, transposeInv_diagonal_real, hab, ← mul_assoc, weyl_mul_diagonal_real, mul_assoc]

end GlobalTheory.CompanionTheory.GL2Factorization.IwasawaDual
