import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CardGeneralLinearGroupPrimeField
import Development.AbelianVarietyTheory.Definitions.Foundations.StandardFiveNontrivial
open Polynomial Classical GlobalTheory.BadShare
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_generalLinearGroup_primeField : ∀ (g : ℕ) [Fact g.Prime] (N : ℕ), Fintype.card (GG g N) = g ^ (N * (N - 1) / 2) * ∏ i ∈ Finset.range N, (g ^ (i + 1) - 1) := by
  first | exact @GlobalTheory.BadShare.card_GG_eq | exact GlobalTheory.BadShare.card_GG_eq | (intros; apply GlobalTheory.BadShare.card_GG_eq <;> assumption)
