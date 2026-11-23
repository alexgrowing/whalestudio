import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeBasisRealBasisOfHolomorphicFamily
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsLatBasisZero
open GlobalTheory.ShFam.Hor.LogCh

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeBasis_realBasis_of_holomorphic_family : ∀ (n g r : ℕ) (B : Set (Fin n → ℂ)) (K : (Fin n → ℂ) → Set (Fin g → ℂ)) (b₀ : Fin n → ℂ) (lam : Fin r → Fin g → ℂ), IsLatFam B K → b₀ ∈ B → Submodule.span ℝ (K b₀) = ⊤ → LinearIndependent ℤ lam → (∀ w, w ∈ K b₀ ↔ ∃ k : Fin r → ℤ, w = ∑ j, k j • lam j) → LinearIndependent ℝ lam ∧ Submodule.span ℝ (Set.range lam) = ⊤ := by
  first | exact @GlobalTheory.LatReal.isRealBasis_of_isLatFam | exact GlobalTheory.LatReal.isRealBasis_of_isLatFam | (intros; apply GlobalTheory.LatReal.isRealBasis_of_isLatFam <;> assumption)
