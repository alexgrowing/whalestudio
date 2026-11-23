import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsNearestPointCosetOrthogonalLieAlgebra
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableSetHsBall
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nearest_point_coset_orthogonal_lieAlgebra : ∀ (n : ℕ) (ε : Fin n → Bool) (S : Set (Formalism.REAL.UJ ε)) (d : ℕ) (E : Fin d → Matrix (Fin n) (Fin n) ℂ), IsCut ε S E → S ⊆ maxK ε → (∀ i, (E i)ᴴ = -E i) → ∀ k ∈ maxK ε, ∃ l ∈ S, crd E (uMat (l * k) - 1) = 0 ∧ ∀ l' ∈ S, nrm (uMat (l * k) - 1) ≤ nrm (uMat (l' * k) - 1) := by
  first | exact @GlobalTheory.IwConstMin.exists_nearest | exact GlobalTheory.IwConstMin.exists_nearest | (intros; apply GlobalTheory.IwConstMin.exists_nearest <;> assumption)
