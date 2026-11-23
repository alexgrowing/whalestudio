import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicCompletionLatticeSeparatedComplete
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Matrix nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicCompletion_lattice_separated_complete : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)), L.FG → (∀ z : Fin n → RA F E, (∀ N : ℕ, 0 < N → ∃ w ∈ (hat F (L : Set (Fin n → E))), z = N • w) → z = 0) ∧ ∀ x : ℕ → (Fin n → RA F E), (∀ N, x N ∈ (hat F (L : Set (Fin n → E)))) → (∀ N m : ℕ, 0 < N → 0 < m → ∃ w ∈ (hat F (L : Set (Fin n → E))), x (N * m) = x N + N • w) → ∃ z ∈ (hat F (L : Set (Fin n → E))), ∀ N : ℕ, 0 < N → ∃ w ∈ (hat F (L : Set (Fin n → E))), z = x N + N • w := by
  first | exact @GlobalTheory.AdLat.Complete.hat_separated_complete | exact GlobalTheory.AdLat.Complete.hat_separated_complete | (intros; apply GlobalTheory.AdLat.Complete.hat_separated_complete <;> assumption)
