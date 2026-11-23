import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.UnitaryLieGeneratorsRep
import Formalism.SatakeDualWeyl.Statement
import Formalism.FormalDegreeBessel.StatementG
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IntegralConjInnerMulInnerOfIsEmptyEquiv
open Matrix

namespace GlobalTheory.DefiniteFrame

theorem exists_frame {n p q : ℕ} {J : Matrix (Fin n) (Fin n) ℂ} (h : Formalism.UG.HasSignature J p q) :
    ∃ (e : Fin n ≃ Fin p ⊕ Fin q) (B : Matrix (Fin n) (Fin n) ℂ), IsUnit B.det ∧
      J = Bᴴ * (Formalism.UG.Jpq p q).submatrix e e * B := by
  obtain ⟨e, P, hP⟩ := h
  have hP' : P.valᴴ * (reindex e e J) * P.val = Formalism.UG.Jpq p q := hP
  refine ⟨e, (P⁻¹).val.submatrix e e, ?_, ?_⟩
  · rw [det_submatrix_equiv_self]
    exact (Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit _)
  · have h1 := Units.mul_inv P
    have h2 : (P⁻¹).valᴴ * P.valᴴ = 1 := by
      rw [← conjTranspose_mul, h1, conjTranspose_one]
    rw [conjTranspose_submatrix, submatrix_mul_equiv, submatrix_mul_equiv, ← hP']
    have h3 : (P⁻¹).valᴴ *
        (P.valᴴ * (reindex e e J) * P.val) *
        (P⁻¹).val = reindex e e J := by
      calc _ = ((P⁻¹).valᴴ * P.valᴴ) * (reindex e e J) *
          (P.val * (P⁻¹).val) := by
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]
    rw [h3]
    ext i j
    simp

theorem isCompact_UH_gram {n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ) (hB : IsUnit B.det) :
    IsCompact (Formalism.QuantumDeterminants.UH (Bᴴ * B)) := by
  have hc : Continuous fun u : Matrix (Fin n) (Fin n) ℂ => B⁻¹ * u * B :=
    (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  have h1 : B * B⁻¹ = 1 := mul_nonsing_inv B hB
  have h1' : B⁻¹ * B = 1 := nonsing_inv_mul B hB
  have h2 : (B⁻¹)ᴴ * Bᴴ = 1 := by rw [← conjTranspose_mul, h1, conjTranspose_one]
  have h2' : Bᴴ * (B⁻¹)ᴴ = 1 := by rw [← conjTranspose_mul, h1', conjTranspose_one]
  convert (GlobalTheory.isCompact_unitaryGroup (Fin n) ℂ).image hc using 1
  ext g
  simp only [Formalism.QuantumDeterminants.UH, Set.mem_ofPred_eq, Set.mem_image, SetLike.mem_coe,
    Matrix.mem_unitaryGroup_iff', star_eq_conjTranspose]
  constructor
  · intro hg
    refine ⟨B * g * B⁻¹, ?_, ?_⟩
    · calc (B * g * B⁻¹)ᴴ * (B * g * B⁻¹) = (B⁻¹)ᴴ * (gᴴ * (Bᴴ * B) * g) * B⁻¹ := by
            simp only [conjTranspose_mul, Matrix.mul_assoc]
        _ = ((B⁻¹)ᴴ * Bᴴ) * (B * B⁻¹) := by rw [hg]; simp only [Matrix.mul_assoc]
        _ = 1 := by rw [h1, h2, Matrix.one_mul]
    · calc B⁻¹ * (B * g * B⁻¹) * B = (B⁻¹ * B) * g * (B⁻¹ * B) := by
            simp only [Matrix.mul_assoc]
        _ = g := by rw [h1', Matrix.one_mul, Matrix.mul_one]
  · rintro ⟨u, hu, rfl⟩
    calc (B⁻¹ * u * B)ᴴ * (Bᴴ * B) * (B⁻¹ * u * B)
        = Bᴴ * (uᴴ * ((B⁻¹)ᴴ * Bᴴ) * (B * B⁻¹) * u) * B := by
          simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = Bᴴ * B := by rw [h1, h2, Matrix.mul_one, Matrix.mul_one, hu, Matrix.mul_one]

theorem UH_neg {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) : Formalism.QuantumDeterminants.UH (-H) = Formalism.QuantumDeterminants.UH H := by
  ext g
  simp [Formalism.QuantumDeterminants.UH]

theorem definite_frame (n p q : ℕ) (J : Matrix (Fin n) (Fin n) ℂ)
    (h : Formalism.UG.HasSignature J p q) (hpq : p = 0 ∨ q = 0) :
    (∃ B : Matrix (Fin n) (Fin n) ℂ, IsUnit B.det ∧ (J = Bᴴ * B ∨ J = -(Bᴴ * B))) ∧
      IsCompact (Formalism.QuantumDeterminants.UH J) := by
  obtain ⟨e, B, hB, hJ⟩ := exists_frame h
  rcases hpq with rfl | rfl
  · have h1 : Formalism.UG.Jpq 0 q = -1 := by
      ext i j
      rcases i with i | i
      · exact i.elim0
      rcases j with j | j
      · exact j.elim0
      simp [Formalism.UG.Jpq, Matrix.one_apply]
    have h2 : J = -(Bᴴ * B) := by
      rw [hJ, h1, submatrix_neg]
      simp
    refine ⟨⟨B, hB, Or.inr h2⟩, ?_⟩
    rw [h2, UH_neg]
    exact isCompact_UH_gram B hB
  · have h1 : Formalism.UG.Jpq p 0 = 1 := by
      ext i j
      rcases i with i | i
      swap
      · exact i.elim0
      rcases j with j | j
      swap
      · exact j.elim0
      simp [Formalism.UG.Jpq, Matrix.one_apply]
    have h2 : J = Bᴴ * B := by
      rw [hJ, h1]
      simp
    refine ⟨⟨B, hB, Or.inl h2⟩, ?_⟩
    rw [h2]
    exact isCompact_UH_gram B hB

end GlobalTheory.DefiniteFrame
