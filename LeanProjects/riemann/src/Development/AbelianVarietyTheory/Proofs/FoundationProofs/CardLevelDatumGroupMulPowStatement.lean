import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CardLevelDatumGroupMulPow
import Development.AbelianVarietyTheory.Definitions.Foundations.StandardFiveNontrivial
open Polynomial Classical GlobalTheory.BadShare
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_levelDatum_group_mul_pow : ∀ (g : ℕ) [Fact g.Prime] (N : ℕ), ∀ L : Lev g N, Nat.card {u // L.Mem u} * g ^ (if L.sharp = true then L.k else 0) = g ^ (N * (N - 1) / 2) := by
  first | exact @GlobalTheory.BadShare.lev_card | exact GlobalTheory.BadShare.lev_card | (intros; apply GlobalTheory.BadShare.lev_card <;> assumption)
