import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BrauerNesbittSemisimpleMatrixRepresentations
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.brauer_nesbitt_semisimple_matrix_representations : ∀ {k G : Type} [Field k] [Group G] (n : ℕ) (ρ σ : G →* Matrix (Fin n) (Fin n) k), (∀ W : Submodule k (Fin n → k), (∀ g, ∀ v ∈ W, (ρ g).mulVec v ∈ W) → ∃ W', IsCompl W W' ∧ ∀ g, ∀ v ∈ W', (ρ g).mulVec v ∈ W') → (∀ W : Submodule k (Fin n → k), (∀ g, ∀ v ∈ W, (σ g).mulVec v ∈ W) → ∃ W', IsCompl W W' ∧ ∀ g, ∀ v ∈ W', (σ g).mulVec v ∈ W') → (∀ g, (ρ g).charpoly = (σ g).charpoly) → ∃ P : GL (Fin n) k, ∀ g, (P : Matrix (Fin n) (Fin n) k) * ρ g = σ g * P := by
  first | exact @GlobalTheory.BrauerNesbittMatrix.main | exact GlobalTheory.BrauerNesbittMatrix.main | (intros; apply GlobalTheory.BrauerNesbittMatrix.main <;> assumption)
