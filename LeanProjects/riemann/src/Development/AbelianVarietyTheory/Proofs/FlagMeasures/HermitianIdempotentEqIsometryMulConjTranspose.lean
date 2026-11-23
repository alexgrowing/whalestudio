import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsGaugeAll

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory

theorem hermitian_idempotent_eq_isometry_mul_conjTranspose :
    ∀ (n : ℕ) (R : Matrix (Fin n) (Fin n) ℂ), Rᴴ = R → R * R = R →
      ∃ (r : ℕ) (P : Matrix (Fin n) (Fin r) ℂ), Pᴴ * P = 1 ∧ P * Pᴴ = R := by
  intro n R hH hI
  classical
  have hA : R.IsHermitian := hH
  have hev : ∀ i, hA.eigenvalues i = 0 ∨ hA.eigenvalues i = 1 := by
    intro i
    have hv := hA.mulVec_eigenvectorBasis i
    have hne : (⇑(hA.eigenvectorBasis i) : Fin n → ℂ) ≠ 0 :=
      (WithLp.ofLp_eq_zero 2).ne.2 (hA.eigenvectorBasis.orthonormal.ne_zero i)
    have h2 : R *ᵥ (R *ᵥ ⇑(hA.eigenvectorBasis i)) = R *ᵥ ⇑(hA.eigenvectorBasis i) := by
      rw [mulVec_mulVec, hI]
    rw [hv, mulVec_smul, hv, smul_smul] at h2
    have h3 : (hA.eigenvalues i * hA.eigenvalues i - hA.eigenvalues i) •
        (⇑(hA.eigenvectorBasis i) : Fin n → ℂ) = 0 := by
      rw [sub_smul, h2, sub_self]
    rcases smul_eq_zero.mp h3 with h | h
    · have h4 : hA.eigenvalues i * (hA.eigenvalues i - 1) = 0 := by linear_combination h
      rcases mul_eq_zero.mp h4 with h' | h'
      · exact Or.inl h'
      · exact Or.inr (by linarith)
    · exact absurd h hne
  set U : Matrix (Fin n) (Fin n) ℂ := (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) with hUdef
  have hU : Uᴴ * U = 1 := Unitary.coe_star_mul_self hA.eigenvectorUnitary
  let e : Fin (Fintype.card {i // hA.eigenvalues i ≠ 0}) ≃ {i // hA.eigenvalues i ≠ 0} :=
    (Fintype.equivFin _).symm
  let f : Fin (Fintype.card {i // hA.eigenvalues i ≠ 0}) → Fin n := fun j => (e j).1
  have hf : Function.Injective f := Subtype.val_injective.comp e.injective
  let Q : Matrix (Fin n) (Fin (Fintype.card {i // hA.eigenvalues i ≠ 0})) ℂ :=
    (1 : Matrix (Fin n) (Fin n) ℂ).submatrix id f
  have hQQ : Qᴴ * Q = 1 := by
    ext j k
    simp [Q, Matrix.mul_apply, Matrix.one_apply, hf.eq_iff]
  have hQ : Q * Qᴴ = diagonal (RCLike.ofReal ∘ hA.eigenvalues) := by
    ext i k
    rw [Matrix.mul_apply, diagonal_apply]
    simp only [Q, conjTranspose_apply, submatrix_apply, id, Matrix.one_apply, Function.comp_apply]
    by_cases h0 : hA.eigenvalues i = 0
    · have hz : ∀ j, (if i = f j then (1 : ℂ) else 0) = 0 := by
        intro j
        refine if_neg (fun h => (e j).2 ?_)
        rw [show (e j).1 = i from h.symm]
        exact h0
      simp only [hz, zero_mul, Finset.sum_const_zero, h0]
      split_ifs <;> simp
    · have h1 : hA.eigenvalues i = 1 := (hev i).resolve_left h0
      have hj0 : f (e.symm ⟨i, h0⟩) = i := by simp [f]
      rw [Finset.sum_eq_single (e.symm ⟨i, h0⟩)]
      · rw [hj0, if_pos rfl, one_mul, h1]
        by_cases hik : i = k
        · subst hik
          simp
        · rw [if_neg (Ne.symm hik), if_neg hik]
          simp
      · intro b _ hb
        have hne : i ≠ f b := by
          intro h
          apply hb
          rw [Equiv.eq_symm_apply]
          exact Subtype.ext h.symm
        rw [if_neg hne, zero_mul]
      · intro h
        exact absurd (Finset.mem_univ _) h
  refine ⟨Fintype.card {i // hA.eigenvalues i ≠ 0}, U * Q, ?_, ?_⟩
  · rw [conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Uᴴ, hU, Matrix.one_mul, hQQ]
  · have hs := hA.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at hs
    rw [conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Q, hQ]
    conv_rhs => rw [hs]
    simp [U, Matrix.mul_assoc, Matrix.star_eq_conjTranspose]

end GlobalTheory
