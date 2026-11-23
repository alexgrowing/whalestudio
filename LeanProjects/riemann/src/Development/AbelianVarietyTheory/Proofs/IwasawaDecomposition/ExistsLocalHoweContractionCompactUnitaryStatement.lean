import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalHoweContractionCompactUnitary
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import ReciprocityTheory.DualLattices.FischerSelfNeZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TotalDegreeSubstFLe
open Formalism.MainNotions.S Matrix GlobalTheory.CompactHowe
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_local_howe_contraction_compact_unitary : ∀ (N n : ℕ) (hn : n ≤ N) (ν : Fin N → ℕ) (x₁ x₃ : ℤ) (Λ : Fin n → ℝ) (Λ' : Fin N → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (H' : Type) [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [FiniteDimensional ℂ H'] (σ' : Matrix (Fin N) (Fin N) ℂ → (H' →L[ℂ] H')), Antitone ν → (∀ b : Fin N, n ≤ (b : ℕ) → ν b = 0) → (∀ a, Λ a = (x₃ : ℝ) - ν (Fin.castLE hn (Fin.rev a))) → (∀ b, Λ' b = -(x₁ : ℝ) - ν (Fin.rev b)) → IsURepOn (UJset (allPos n)) σ → IsKTypeOf (allPos n) σ Λ ⊤ → IsURepOn (UJset (allPos N)) σ' → IsKTypeOf (allPos N) σ' Λ' ⊤ → ∃ I : MvPolynomial (Fin N × Fin n) ℂ →ₗ[ℂ] H' →ₗ[ℂ] H, I ≠ 0 ∧ ∀ h ∈ UJset (allPos N), ∀ g ∈ UJset (allPos n), ∀ P v, I ((h.det ^ x₁ * g.det ^ x₃) • subst2 h (g⁻¹)ᵀ P) (σ' h v) = σ g (I P v) := by
  first | exact @GlobalTheory.CompactHowe.exists_local_contraction | exact GlobalTheory.CompactHowe.exists_local_contraction | (intros; apply GlobalTheory.CompactHowe.exists_local_contraction <;> assumption)
