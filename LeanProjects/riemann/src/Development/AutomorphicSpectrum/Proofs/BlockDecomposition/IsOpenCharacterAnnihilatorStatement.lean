import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsOpenCharacterAnnihilator
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isOpen_character_annihilator : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ∀ (n : ℕ) (A : AddSubgroup (Fin n → k)), IsCompact (A : Set (Fin n → k)) → IsOpen {ξ : Fin n → k | ∀ a ∈ A, ψ (ξ ⬝ᵥ a) = 1} := by
  first | exact @GlobalTheory.CompanionTheory.AnnihOpen.isOpen_annihilator_of_isCompact | exact GlobalTheory.CompanionTheory.AnnihOpen.isOpen_annihilator_of_isCompact | (intros; apply GlobalTheory.CompanionTheory.AnnihOpen.isOpen_annihilator_of_isCompact <;> assumption)
