import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsOrthonormalLieCoordinates
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IpLEqZeroOfMemSpan
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_orthonormal_lie_coordinates : ∀ (n d m : ℕ) (ε : Fin n → Bool) (A : ℕ → Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) (E : Fin d → Matrix (Fin n) (Fin n) ℂ), A m = ⊥ → (∀ c, ∀ X ∈ A c, ∀ Y ∈ A 0, X * Y ∈ A (c + 1) ∧ Y * X ∈ A (c + 1)) → (∀ c, A (c + 1) ≤ A c) → (∀ c, ∀ X ∈ A c, Formalism.REAL.Jm ε * Xᴴ * Formalism.REAL.Jm ε ∈ A c) → (∀ i k, ((E i * (E k)ᴴ).trace).re = if i = k then 1 else 0) → (∀ i, E i ∈ A 0 ∧ Formalism.REAL.inG ε (E i)) → ∃ σ : (Fin d → ℝ) → Formalism.REAL.UJ ε, Continuous σ ∧ ∀ x, uMat (σ x) - 1 ∈ A 0 ∧ ∀ i, (((uMat (σ x) - 1) * (E i)ᴴ).trace).re = x i := by
  first | exact @GlobalTheory.NilCovSec.exists_continuous_section | exact GlobalTheory.NilCovSec.exists_continuous_section | (intros; apply GlobalTheory.NilCovSec.exists_continuous_section <;> assumption)
