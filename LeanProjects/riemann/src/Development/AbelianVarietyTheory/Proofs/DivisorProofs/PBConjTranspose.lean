import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.RangeShape

noncomputable section

open Formalism.REAL (UJ KG toM inG Jm)
open GlobalTheory.PsCo.Pc1
open scoped Matrix

namespace GlobalTheory.PsCo.Pc3

variable {n : ℕ}

theorem pB_conjTranspose (ε : Fin n → Bool) (B : Mode ε → ℂ) : (pB ε B)ᴴ = pB ε B := by
  ext a b
  simp only [Matrix.conjTranspose_apply]
  cases ha : ε a <;> cases hb : ε b <;> simp [pB, ha, hb]

theorem pB_ne (ε : Fin n → Bool) (B : Mode ε → ℂ) (a b : Fin n) (h : ε a = ε b) : pB ε B a b = 0 := by
  simp only [pB]
  rw [dif_neg (by rintro ⟨h1, h2⟩; rw [h, h2] at h1; simp at h1),
    dif_neg (by rintro ⟨h1, h2⟩; rw [← h, h2] at h1; simp at h1)]

theorem pB_inG (ε : Fin n → Bool) (B : Mode ε → ℂ) : inG ε (pB ε B) := by
  unfold inG
  rw [pB_conjTranspose]
  ext a b
  simp only [Matrix.add_apply, Matrix.zero_apply, Jm, Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases h : ε a = ε b
  · rw [pB_ne ε B a b h]; simp
  · cases ha : ε a <;> cases hb : ε b <;> simp_all

theorem continuous_pB (ε : Fin n → Bool) : Continuous (pB ε) := by
  refine continuous_pi fun a => continuous_pi fun b => ?_
  simp only [pB]
  split_ifs
  · exact continuous_apply _
  · exact (continuous_apply _).star
  · exact continuous_const

theorem pB_zero (ε : Fin n → Bool) : pB ε 0 = 0 := by
  ext a b; simp only [pB]; split_ifs <;> simp

theorem toM_eB (ε : Fin n → Bool) (B : Mode ε → ℂ) : toM (eB ε B) = NormedSpace.exp (pB ε B) := by
  rw [eB, Formalism.REAL.toM_expG ε _ 1 (pB_inG ε B)]; simp

theorem toM_inv (ε : Fin n → Bool) (g : UJ ε) : toM g⁻¹ = (toM g)⁻¹ := by
  show (((g : (Matrix (Fin n) (Fin n) ℂ)ˣ)⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) = _
  rw [Matrix.coe_units_inv]

theorem stEB : StEB := by
  intro n ε
  refine ⟨?_, ?_, fun B => ⟨toM_eB ε B, ?_⟩⟩
  · rw [(Formalism.REAL.isClosedEmbeddingMatrix n ε).1.isEmbedding.continuous_iff]
    change Continuous fun B => toM (eB ε B)
    simp_rw [toM_eB]
    have hc : Continuous (NormedSpace.exp : Mat n → Mat n) := by
      letI := Matrix.linftyOpNormedRing (n := Fin n) (α := ℂ)
      letI := Matrix.linftyOpNormedAlgebra (n := Fin n) (R := ℚ) (α := ℂ)
      exact @NormedSpace.exp_continuous (Matrix (Fin n) (Fin n) ℂ) _ _
        (inferInstanceAs (CompleteSpace (Fin n → Fin n → ℂ)))
    exact hc.comp (continuous_pB ε)
  · apply Subtype.ext; apply Units.ext
    change toM (eB ε 0) = 1
    rw [toM_eB, pB_zero, NormedSpace.exp_zero]
  · rw [toM_inv, toM_eB]
    rw [Matrix.exp_neg]

end GlobalTheory.PsCo.Pc3
