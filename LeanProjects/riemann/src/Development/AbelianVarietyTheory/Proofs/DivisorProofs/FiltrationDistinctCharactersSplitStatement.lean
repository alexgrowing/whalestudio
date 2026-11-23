import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiltrationDistinctCharactersSplit
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusThreeBlockApply
open GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.LeviBlockExponent GlobalTheory.IndJacBlock
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.filtration_distinct_characters_split : ∀ {V : Type} [AddCommGroup V] [Module ℂ V] {G : Type} [CommMonoid G] (ρ : G →* Module.End ℂ V)
    (M : ℕ) (S : Fin (M + 1) → Submodule ℂ V) (c : Fin M → G → ℂ), Monotone S → S 0 = ⊥ →
    (∀ t : Fin M, ∀ v ∈ S t.succ, ∀ g, ρ g v - c t g • v ∈ S t.castSucc) →
    (∀ s t, s ≠ t → ∃ g, c s g ≠ c t g) →
    ∀ v ∈ S (Fin.last M), ∃ w : Fin M → V, v = ∑ t, w t ∧ ∀ t g, ρ g (w t) = c t g • w t := by
  first | exact @GlobalTheory.ChainSplit.chain_split | exact GlobalTheory.ChainSplit.chain_split | (intros; apply GlobalTheory.ChainSplit.chain_split <;> assumption)
