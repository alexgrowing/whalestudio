import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobData

open scoped Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.DCell

open Matrix PositivityTheory.Rg.Sw

variable {n : ℕ}

theorem JJ_mul_self : JJ n * JJ n = -1 := by
  rw [JJ, fromBlocks_multiply, ← fromBlocks_one, fromBlocks_neg]
  simp

theorem rows_rel (g : M2 n) (h : InG g) : g * JJ n * gᴴ = JJ n := by
  have hinv : (-(JJ n) * gᴴ * JJ n) * g = 1 := by
    have h' : gᴴ * JJ n * g = JJ n := h
    calc (-(JJ n) * gᴴ * JJ n) * g = -(JJ n * (gᴴ * JJ n * g)) := by
          simp only [Matrix.mul_assoc, Matrix.neg_mul]
      _ = 1 := by rw [h', JJ_mul_self, neg_neg]
  have h2 : g * (-(JJ n) * gᴴ * JJ n) = 1 := mul_eq_one_comm.mp hinv
  calc g * JJ n * gᴴ = g * JJ n * gᴴ * (-(JJ n * JJ n)) := by
        rw [JJ_mul_self, neg_neg, Matrix.mul_one]
    _ = -((g * (-(JJ n) * gᴴ * JJ n)) * JJ n) * (-1) * (-1) * (-1) := by
        simp only [Matrix.mul_assoc, Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_one, neg_neg]
    _ = JJ n := by
        rw [h2]; simp

theorem block_rel (g : M2 n) (h : InG g) :
    g.toBlocks₂₁ * g.toBlocks₂₂ᴴ = g.toBlocks₂₂ * g.toBlocks₂₁ᴴ := by
  have h1 := rows_rel g h
  have h3 : (g * JJ n * gᴴ).toBlocks₂₂ = (JJ n).toBlocks₂₂ := by rw [h1]
  rw [← fromBlocks_toBlocks g] at h3
  simp only [JJ, fromBlocks_conjTranspose, fromBlocks_multiply, toBlocks_fromBlocks₂₂] at h3
  simp at h3
  have h4 := sub_eq_zero.mp (by
    rw [← h3]; abel : g.toBlocks₂₁ * g.toBlocks₂₂ᴴ - g.toBlocks₂₂ * g.toBlocks₂₁ᴴ = 0)
  exact h4

theorem inG_lower (c : Matrix (Fin n) (Fin n) ℂ) (hc : cᴴ = c) :
    InG (fromBlocks 1 0 c 1 : M2 n) := by
  unfold InG
  rw [JJ, fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply]
  simp [hc]

def lowerU (c : Matrix (Fin n) (Fin n) ℂ) : GL (Fin n ⊕ Fin n) ℂ where
  val := fromBlocks 1 0 c 1
  inv := fromBlocks 1 0 (-c) 1
  val_inv := by rw [fromBlocks_multiply, ← fromBlocks_one]; simp
  inv_val := by rw [fromBlocks_multiply, ← fromBlocks_one]; simp

theorem main : ∀ (n : ℕ) (y : PositivityTheory.Rg.Sw.GR n), ((PositivityTheory.Rg.Sw.mR y).toBlocks₂₂).det ≠ 0 → ∃ (p nbb : PositivityTheory.Rg.Sw.GR n) (c : Matrix (Fin n) (Fin n) ℂ), (PositivityTheory.Rg.Sw.mR p).toBlocks₂₁ = 0 ∧ cᴴ = c ∧ PositivityTheory.Rg.Sw.mR nbb = Matrix.fromBlocks 1 0 c 1 ∧ y = p * nbb := by
  intro n y hD
  set g : M2 n := mR y with hg
  have hy : InG g := y.2
  set C := g.toBlocks₂₁ with hC
  set D := g.toBlocks₂₂ with hDd
  have hrel : C * Dᴴ = D * Cᴴ := block_rel g hy
  have hu : IsUnit D.det := isUnit_iff_ne_zero.mpr hD
  have hDi : D * D⁻¹ = 1 := Matrix.mul_nonsing_inv D hu
  have hiD : D⁻¹ * D = 1 := Matrix.nonsing_inv_mul D hu
  have hiDH : (D⁻¹)ᴴ * Dᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, hDi, Matrix.conjTranspose_one]
  have hc : (D⁻¹ * C)ᴴ = D⁻¹ * C := by
    rw [Matrix.conjTranspose_mul]
    have hDH : Dᴴ * (D⁻¹)ᴴ = 1 := mul_eq_one_comm.mp hiDH
    calc Cᴴ * (D⁻¹)ᴴ = (D⁻¹ * D) * Cᴴ * (D⁻¹)ᴴ := by rw [hiD, Matrix.one_mul]
      _ = D⁻¹ * (D * Cᴴ) * (D⁻¹)ᴴ := by simp only [Matrix.mul_assoc]
      _ = D⁻¹ * (C * Dᴴ) * (D⁻¹)ᴴ := by rw [hrel]
      _ = D⁻¹ * C * (Dᴴ * (D⁻¹)ᴴ) := by simp only [Matrix.mul_assoc]
      _ = D⁻¹ * C := by rw [hDH, Matrix.mul_one]
  set c := D⁻¹ * C with hcdef
  have hmem : lowerU c ∈ GR n := inG_lower c hc
  refine ⟨y * (⟨lowerU c, hmem⟩ : GR n)⁻¹, ⟨lowerU c, hmem⟩, c, ?_, hc, rfl, by simp⟩
  have hval : mR (y * (⟨lowerU c, hmem⟩ : GR n)⁻¹) = g * fromBlocks 1 0 (-c) 1 := rfl
  rw [hval]
  conv_lhs => rw [← fromBlocks_toBlocks g]
  rw [fromBlocks_multiply, toBlocks_fromBlocks₂₁]
  have : D * c = C := by rw [hcdef, ← Matrix.mul_assoc, hDi, Matrix.one_mul]
  simp [← hC, ← hDd, this]

end GlobalTheory.CompanionTheory.DCell
