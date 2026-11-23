import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPairingStdP
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
open scoped SchwartzMap Matrix

namespace GlobalTheory

open Matrix

theorem sympl_eq_neg_dotProduct_J {l : Type} [Fintype l] [DecidableEq l] (w w' : l ⊕ l → ℝ) :
    GlobalTheory.RealWeil.sympl w w' = -(w ⬝ᵥ (J l ℝ *ᵥ w')) := by
  simp only [GlobalTheory.RealWeil.sympl, GlobalTheory.RealWeil.pPart, GlobalTheory.RealWeil.qPart, J, EuclideanSpace.inner_eq_star_dotProduct]
  simp [dotProduct, Fintype.sum_sum_type, fromBlocks_mulVec, Matrix.one_apply, Finset.sum_neg_distrib, mul_comm, Matrix.neg_mulVec, Matrix.one_mulVec]
  ring

theorem exists_symplecticGroup_of_sympl (l : Type) [Fintype l] [DecidableEq l]
    (ψ : (l ⊕ l → ℝ) →ₗ[ℝ] (l ⊕ l → ℝ))
    (h : ∀ w w', GlobalTheory.RealWeil.sympl (ψ w) (ψ w') = GlobalTheory.RealWeil.sympl w w') :
    ∃ M : Matrix.symplecticGroup l ℝ, ∀ w, (M : Matrix (l ⊕ l) (l ⊕ l) ℝ) *ᵥ w = ψ w := by
  set M := LinearMap.toMatrix' ψ with hM
  have hMv : ∀ w, M *ᵥ w = ψ w := fun w => by rw [hM, LinearMap.toMatrix'_mulVec]
  have key : ∀ w w', w ⬝ᵥ ((Mᵀ * J l ℝ * M) *ᵥ w') = w ⬝ᵥ (J l ℝ *ᵥ w') := by
    intro w w'
    have := h w w'
    rw [sympl_eq_neg_dotProduct_J, sympl_eq_neg_dotProduct_J, ← hMv, ← hMv] at this
    rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]
    linarith
  have hmem : M ∈ Matrix.symplecticGroup l ℝ := by
    rw [SymplecticGroup.mem_iff']
    ext i j
    have := key (Pi.single i 1) (Pi.single j 1)
    simpa [single_dotProduct, mulVec_single] using this
  exact ⟨⟨M, hmem⟩, hMv⟩

end GlobalTheory
