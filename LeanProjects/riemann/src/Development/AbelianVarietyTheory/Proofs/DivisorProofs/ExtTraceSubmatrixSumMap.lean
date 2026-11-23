import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqOfNonneg
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.CurveDens GlobalTheory.Cartier
open scoped ComplexOrder

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.HermFrame.Renumber
open Matrix

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
variable {m l m' l' : Type} [Fintype m] [Fintype l] [Fintype m'] [Fintype l'] [DecidableEq m]
  [DecidableEq l] [DecidableEq m'] [DecidableEq l']

theorem mdbar_submatrix {a b a' b' : Type} (A : E → Matrix a b ℂ) (e : a' → a) (f : b' → b) (z η : E) :
    mdbar (fun x => (A x).submatrix e f) z η = (mdbar A z η).submatrix e f := by
  ext i j; simp [mdbar]

theorem subGram_submatrix (e : m' ≃ m) (f : l' ≃ l) (H : Matrix (m ⊕ l) (m ⊕ l) ℂ) :
    subGram (H.submatrix (Sum.map e f) (Sum.map e f)) = (subGram H).submatrix e e := by
  ext i j; simp [subGram, toBlocks₁₁]

theorem quotGram_submatrix (e : m' ≃ m) (f : l' ≃ l) (H : Matrix (m ⊕ l) (m ⊕ l) ℂ) :
    quotGram (H.submatrix (Sum.map e f) (Sum.map e f)) = (quotGram H).submatrix f f := by
  have h11 : (H.submatrix (Sum.map e f) (Sum.map e f)).toBlocks₁₁ = H.toBlocks₁₁.submatrix e e := by
    ext i j; simp [toBlocks₁₁]
  have h12 : (H.submatrix (Sum.map e f) (Sum.map e f)).toBlocks₁₂ = H.toBlocks₁₂.submatrix e f := by
    ext i j; simp [toBlocks₁₂]
  have h21 : (H.submatrix (Sum.map e f) (Sum.map e f)).toBlocks₂₁ = H.toBlocks₂₁.submatrix f e := by
    ext i j; simp [toBlocks₂₁]
  have h22 : (H.submatrix (Sum.map e f) (Sum.map e f)).toBlocks₂₂ = H.toBlocks₂₂.submatrix f f := by
    ext i j; simp [toBlocks₂₂]
  rw [quotGram, quotGram, h11, h12, h21, h22, inv_submatrix_equiv, submatrix_mul_equiv,
    submatrix_mul_equiv]; rfl

theorem orthCoeff_submatrix (e : m' ≃ m) (f : l' ≃ l) (H : Matrix (m ⊕ l) (m ⊕ l) ℂ) :
    orthCoeff (H.submatrix (Sum.map e f) (Sum.map e f)) = (orthCoeff H).submatrix e f := by
  have h11 : (H.submatrix (Sum.map e f) (Sum.map e f)).toBlocks₁₁ = H.toBlocks₁₁.submatrix e e := by
    ext i j; simp [toBlocks₁₁]
  have h21 : (H.submatrix (Sum.map e f) (Sum.map e f)).toBlocks₂₁ = H.toBlocks₂₁.submatrix f e := by
    ext i j; simp [toBlocks₂₁]
  rw [orthCoeff, orthCoeff, h11, h21, transpose_submatrix, transpose_submatrix, inv_submatrix_equiv,
    submatrix_mul_equiv]

theorem adj_submatrix {a b a' b' : Type} [Fintype a] [Fintype b] [Fintype a'] [Fintype b']
    [DecidableEq a] [DecidableEq a'] (e : a' ≃ a) (f : b' ≃ b)
    (H : Matrix a a ℂ) (K : Matrix b b ℂ) (T : Matrix b a ℂ) :
    adj (H.submatrix e e) (K.submatrix f f) (T.submatrix f e) = (adj H K T).submatrix e f := by
  rw [adj, adj, transpose_submatrix, transpose_submatrix, conjTranspose_submatrix,
    inv_submatrix_equiv, submatrix_mul_equiv, submatrix_mul_equiv]

theorem extForm_submatrix (e : m' ≃ m) (f : l' ≃ l) (K : E → Matrix (m ⊕ l) (m ⊕ l) ℂ) (z η : E) :
    extForm (fun x => (K x).submatrix (Sum.map e f) (Sum.map e f)) z η =
      (extForm K z η).submatrix e f := by
  rw [extForm_eq_neg_mdbar, extForm_eq_neg_mdbar]
  simp_rw [orthCoeff_submatrix]
  rw [mdbar_submatrix]; rfl

theorem extFormAdj_submatrix (e : m' ≃ m) (f : l' ≃ l) (K : E → Matrix (m ⊕ l) (m ⊕ l) ℂ) (z ξ : E) :
    extFormAdj (fun x => (K x).submatrix (Sum.map e f) (Sum.map e f)) z ξ =
      (extFormAdj K z ξ).submatrix f e := by
  rw [extFormAdj, extFormAdj, extForm_submatrix, quotGram_submatrix, subGram_submatrix, adj_submatrix]

end GlobalTheory.HermFrame.Renumber

open Matrix in

theorem GlobalTheory.HermFrame.extTrace_submatrix_sumMap : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] (m l m' l' : Type) [Fintype m] [Fintype l] [Fintype m'] [Fintype l'] [DecidableEq m] [DecidableEq l] [DecidableEq m'] [DecidableEq l'] (e : m' ≃ m) (f : l' ≃ l) (K : E → Matrix (m ⊕ l) (m ⊕ l) ℂ) (z : E), extTrace (fun x => (K x).submatrix (Sum.map e f) (Sum.map e f)) z = extTrace K z := by
  intro E _ _ _ _ m l m' l' _ _ _ _ _ _ _ _ e f K z
  funext ξ η
  rw [extTrace, extTrace, Renumber.extFormAdj_submatrix, Renumber.extForm_submatrix,
    submatrix_mul_equiv]
  congr 1
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.submatrix_apply]
  exact Equiv.sum_comp f (fun i => (extFormAdj K z ξ * extForm K z η) i i)
