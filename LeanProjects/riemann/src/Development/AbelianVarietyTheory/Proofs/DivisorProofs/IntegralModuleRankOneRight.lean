import Mathlib
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemNilRad
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralModuleRankOneLeftStatement
open Matrix GlobalTheory.TorFin

namespace GlobalTheory.TorFin

theorem isIntMod_of_neg_of_le {A : Type} [Ring A] [Algebra ℂ A] {Z Z' : Subalgebra ℂ A} {I I' : Submodule ℂ A} {H : A}
    (hZ : Z' ≤ Z) (hI : I' ≤ I) (h : IsIntMod Z' I' (-H)) : IsIntMod Z I H := by
  obtain ⟨N, hN⟩ := h
  refine ⟨N, ?_⟩
  have hs : Submodule.span ℂ {a | ∃ k < N, ∃ z ∈ Z', a = (-H) ^ k * z} ≤
      Submodule.span ℂ {a | ∃ k < N, ∃ z ∈ Z, a = H ^ k * z} := by
    rw [Submodule.span_le]
    rintro a ⟨k, hk, z, hz, rfl⟩
    have hm : H ^ k * z ∈ Submodule.span ℂ {a | ∃ k < N, ∃ z ∈ Z, a = H ^ k * z} :=
      Submodule.subset_span ⟨k, hk, z, hZ hz, rfl⟩
    rcases neg_one_pow_eq_or A k with e | e
    · rw [SetLike.mem_coe, neg_pow, e, one_mul]; exact hm
    · rw [SetLike.mem_coe, neg_pow, e, neg_one_mul, neg_mul]; exact Submodule.neg_mem _ hm
  have hN' := (sup_le_sup hI hs) hN
  rcases neg_one_pow_eq_or A N with e | e
  · rwa [neg_pow, e, one_mul] at hN'
  · rw [neg_pow, e, neg_one_mul] at hN'; simpa using Submodule.neg_mem _ hN'

theorem intMod_vecMulVec_row : ∀ (n : ℕ) (A : Type) [Ring A] [Algebra ℂ A] (ρ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] A),
    IsLieRep ρ → ∀ v φ : Fin n → ℂ, φ ⬝ᵥ v = 1 →
      IsIntMod (invAlg ρ) (leftIdl ρ {Y | ∃ ψ, ψ ⬝ᵥ v = 0 ∧ Y = vecMulVec v ψ}) (ρ (vecMulVec v φ)) := by
  intro n A _ _ ρ hρ v φ hφ
  obtain ⟨ρ', hρ'⟩ : ∃ ρ' : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] A, ∀ Y, ρ' Y = -ρ Yᵀ :=
    ⟨-(ρ ∘ₗ (transposeLinearEquiv (Fin n) (Fin n) ℂ ℂ).toLinearMap), fun Y => rfl⟩
  have hL : IsLieRep ρ' := by
    intro X Y
    rw [hρ', hρ', hρ', transpose_sub, transpose_mul, transpose_mul, ← map_neg, neg_sub, hρ Xᵀ Yᵀ]
    simp only [neg_mul_neg]
  have h1 := GlobalTheory.T.integral_module_rank_one_left n A ρ' hL φ v (by rw [dotProduct_comm]; exact hφ)
  have e1 : ρ' (vecMulVec φ v) = -ρ (vecMulVec v φ) := by rw [hρ', transpose_vecMulVec]
  rw [e1] at h1
  have hadj : Algebra.adjoin ℂ (Set.range ρ') = Algebra.adjoin ℂ (Set.range ρ) := by
    congr 1; ext a; constructor
    · rintro ⟨Y, rfl⟩; exact ⟨-Yᵀ, by rw [hρ', map_neg]⟩
    · rintro ⟨Y, rfl⟩; exact ⟨-Yᵀ, by rw [hρ', transpose_neg, transpose_transpose, map_neg, neg_neg]⟩
  have hZ : invAlg ρ' ≤ invAlg ρ := by
    intro T hT
    rw [mem_invAlg] at hT ⊢
    refine ⟨hadj ▸ hT.1, fun r g g' hg hr => hT.2 r g'ᵀ gᵀ ?_ ?_⟩
    · rw [← transpose_mul, hg, transpose_one]
    · intro Y
      rw [hρ', hρ', mul_neg, neg_mul, hr,
        show (g'ᵀ * Y * gᵀ)ᵀ = g * Yᵀ * g' by simp [transpose_mul, Matrix.mul_assoc]]
  have hI : leftIdl ρ' {Y | ∃ u, v ⬝ᵥ u = 0 ∧ Y = vecMulVec u v} ≤
      leftIdl ρ {Y | ∃ ψ, ψ ⬝ᵥ v = 0 ∧ Y = vecMulVec v ψ} := by
    unfold leftIdl
    rw [Submodule.span_le]
    rintro a ⟨Y, ⟨u, hu, rfl⟩, w, hw, rfl⟩
    rw [SetLike.mem_coe, hρ', transpose_vecMulVec, neg_mul]
    exact Submodule.neg_mem _ (Submodule.subset_span
      ⟨vecMulVec v u, ⟨u, by rw [dotProduct_comm]; exact hu, rfl⟩, w, hadj ▸ hw, rfl⟩)
  exact isIntMod_of_neg_of_le hZ hI h1

end GlobalTheory.TorFin
