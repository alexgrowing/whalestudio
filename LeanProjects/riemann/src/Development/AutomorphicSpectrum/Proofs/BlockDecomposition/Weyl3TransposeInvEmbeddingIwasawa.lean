import Mathlib
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

noncomputable section
namespace GlobalTheory.CompanionTheory.GL2Factorization.DualIw

theorem emR_coe (h : GL (Fin 2) ℝ) : (GL2LocalData.emR h).val =
    !![h.val 0 0, h.val 0 1, 0; h.val 1 0, h.val 1 1, 0; 0, 0, 1] := by
  have hd : (!![h.val 0 0, h.val 0 1, 0; h.val 1 0, h.val 1 1, 0; 0, 0, 1] :
      Matrix (Fin 3) (Fin 3) ℝ).det ≠ 0 := by
    have h1 : (!![h.val 0 0, h.val 0 1, 0; h.val 1 0, h.val 1 1, 0; 0, 0, 1] :
        Matrix (Fin 3) (Fin 3) ℝ).det = (h.val).det := by
      simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Matrix.det_fin_two, Fin.succAbove]
    rw [h1]
    exact ((Matrix.isUnit_iff_isUnit_det _).1 h.isUnit).ne_zero
  rw [GL2LocalData.emR, dif_pos hd]
  rfl

theorem emR_mul (g h : GL (Fin 2) ℝ) : GL2LocalData.emR (g * h) = GL2LocalData.emR g * GL2LocalData.emR h := by
  apply Units.ext
  rw [Units.val_mul, emR_coe, emR_coe, emR_coe, Units.val_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three]

theorem tinvR_mul {n : ℕ} (g h : GL (Fin n) ℝ) : GL2LocalData.tinvR (g * h) = GL2LocalData.tinvR g * GL2LocalData.tinvR h := by
  apply Units.ext
  show ((g * h)⁻¹ : GL (Fin n) ℝ).val.transpose =
    (g⁻¹ : GL (Fin n) ℝ).val.transpose * (h⁻¹ : GL (Fin n) ℝ).val.transpose
  rw [_root_.mul_inv_rev, Units.val_mul, Matrix.transpose_mul]

theorem tinvR_of_orthogonal {n : ℕ} (g : GL (Fin n) ℝ) (hg : g.val * g.valᵀ = 1) :
    GL2LocalData.tinvR g = g := by
  apply Units.ext
  show (g⁻¹ : GL (Fin n) ℝ).val.transpose = g.val
  have h : (g⁻¹ : GL (Fin n) ℝ).val = g.valᵀ := by
    have h1 : (g⁻¹ : GL (Fin n) ℝ).val * g.val = 1 := by
      rw [← Units.val_mul, inv_mul_cancel]; rfl
    calc (g⁻¹ : GL (Fin n) ℝ).val = (g⁻¹ : GL (Fin n) ℝ).val * (g.val * g.valᵀ) := by
          rw [hg, Matrix.mul_one]
      _ = g.valᵀ := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  rw [h, Matrix.transpose_transpose]

theorem emR_orthogonal (k : GL (Fin 2) ℝ) (hk : k.val * k.valᵀ = 1) :
    (GL2LocalData.emR k).val * (GL2LocalData.emR k).valᵀ = 1 := by
  have e : ∀ i j, (k.val * k.valᵀ) i j = (1 : Matrix (Fin 2) (Fin 2) ℝ) i j := fun i j => by rw [hk]
  have e00 := e 0 0
  have e01 := e 0 1
  have e10 := e 1 0
  have e11 := e 1 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10 e11
  rw [emR_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, e00, e01, e10, e11]

theorem weyl3_mul_embedding_mem_orthogonal (k : GL (Fin 2) ℝ) (hk : k.val * k.valᵀ = 1) : GL2LocalData.w3R * GL2LocalData.emR k ∈ O3 := by
  have hw : GL2LocalData.w3R.val * GL2LocalData.w3R.valᵀ = 1 := by
    show (!![0, 0, 1; 0, 1, 0; 1, 0, 0] : Matrix (Fin 3) (Fin 3) ℝ) *
      (!![0, 0, 1; 0, 1, 0; 1, 0, 0] : Matrix (Fin 3) (Fin 3) ℝ)ᵀ = 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  show (GL2LocalData.w3R * GL2LocalData.emR k).val * (GL2LocalData.w3R * GL2LocalData.emR k).valᵀ = 1
  rw [Units.val_mul, Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (GL2LocalData.emR k).val,
    emR_orthogonal k hk, Matrix.one_mul, hw]

theorem dg_mul_dg (a b c d e f : ℝˣ) :
    (dg a b c : GL (Fin 3) ℝ) * dg d e f = dg (a * d) (b * e) (c * f) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dg, Matrix.mul_apply, Fin.sum_univ_three]

theorem weyl3_transposeInv_embedding_diagonal (x y : ℝˣ) :
    GL2LocalData.w3R * GL2LocalData.tinvR (GL2LocalData.emR (dg2 x y)) = dg 1 y⁻¹ x⁻¹ * GL2LocalData.w3R := by
  have hinv : (GL2LocalData.emR (dg2 x y))⁻¹ = GL2LocalData.emR (dg2 x⁻¹ y⁻¹) := by
    apply inv_eq_of_mul_eq_one_right
    rw [← emR_mul]
    apply Units.ext
    rw [emR_coe]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [dg2]
  apply Units.ext
  have h : (GL2LocalData.tinvR (GL2LocalData.emR (dg2 x y))).val = (GL2LocalData.emR (dg2 x⁻¹ y⁻¹)).val.transpose := by
    show ((GL2LocalData.emR (dg2 x y))⁻¹ : GL (Fin 3) ℝ).val.transpose = _
    rw [hinv]
  rw [Units.val_mul, Units.val_mul, h, emR_coe]
  show (!![0, 0, 1; 0, 1, 0; 1, 0, 0] : Matrix (Fin 3) (Fin 3) ℝ) * _ =
    (!![((1 : ℝˣ) : ℝ), 0, 0; 0, ((y⁻¹ : ℝˣ) : ℝ), 0; 0, 0, ((x⁻¹ : ℝˣ) : ℝ)] : Matrix (Fin 3) (Fin 3) ℝ) *
      !![0, 0, 1; 0, 1, 0; 1, 0, 0]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, dg2]

theorem dual_coords : ∀ (a b : ℝˣ) (k : GL (Fin 2) ℝ), k.val * k.valᵀ = 1 → ∃ o ∈ O3,
    GL2LocalData.w3R * GL2LocalData.tinvR (GL2LocalData.emR (dg2 (a * b) b * k)) =
      dg (a * b)⁻¹ (a * b)⁻¹ (a * b)⁻¹ * (dg (b * a) a 1 * o) := by
  intro a b k hk
  refine ⟨GL2LocalData.w3R * GL2LocalData.emR k, weyl3_mul_embedding_mem_orthogonal k hk, ?_⟩
  have h3 : (a * b)⁻¹ * (b * a) = 1 := by rw [mul_comm b a, inv_mul_cancel]
  have h4 : (a * b)⁻¹ * a = b⁻¹ := by rw [_root_.mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]
  rw [emR_mul, tinvR_mul, tinvR_of_orthogonal _ (emR_orthogonal k hk), ← mul_assoc,
    weyl3_transposeInv_embedding_diagonal, ← mul_assoc, dg_mul_dg, h3, h4, mul_one, mul_assoc]

end GlobalTheory.CompanionTheory.GL2Factorization.DualIw
