import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LevelDatumIdempotentRankGeOfGenericFreeRowsFirst
import Development.AbelianVarietyTheory.Definitions.Foundations.StandardFiveNontrivial
open Polynomial Classical GlobalTheory.BadShare
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelDatum_idempotent_rank_ge_of_generic_free_rows_first : ∀ (g : ℕ) [Fact g.Prime] (N : ℕ), ∀ (M : Type) [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M] (ρ : Representation ℂ (GG g N) M), IsGeneric ρ → ∀ L : Lev g N, L.sharp = true → L.s = 0 → (1 - 1 / (g : ℝ)) * (g : ℝ) ^ L.k ≤ (rk ρ L.e : ℝ) := by
  first | exact @GlobalTheory.BadShare.rk_ge_of_isGeneric_of_s_eq_zero | exact GlobalTheory.BadShare.rk_ge_of_isGeneric_of_s_eq_zero | (intros; apply GlobalTheory.BadShare.rk_ge_of_isGeneric_of_s_eq_zero <;> assumption)
