import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AnnihilatorCompactWithinNhds
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.annihilator_compact_within_nhds : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (n : ℕ) (S : Set (Fin n → k)), S ∈ nhds (0 : Fin n → k) → ∃ Ξ : AddSubgroup (Fin n → k), IsCompact (Ξ : Set (Fin n → k)) ∧ ∀ t : Fin n → k, (∀ ξ ∈ Ξ, ψ (ξ ⬝ᵥ t) = 1) → t ∈ S := by
  first | exact @GlobalTheory.CompanionTheory.CharDual.exists_compact_annihilator_subset | exact GlobalTheory.CompanionTheory.CharDual.exists_compact_annihilator_subset | (intros; apply GlobalTheory.CompanionTheory.CharDual.exists_compact_annihilator_subset <;> assumption)
