import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RankLevelDatumIdempotentEqOfSameShape
import Development.AbelianVarietyTheory.Definitions.Foundations.StandardFiveNontrivial
open Polynomial Classical GlobalTheory.BadShare
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rank_levelDatum_idempotent_eq_of_same_shape : ∀ (g : ℕ) [Fact g.Prime] (N : ℕ), ∀ (M : Type) [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M] (ρ : Representation ℂ (GG g N) M), ∀ L L' : Lev g N, L.sharp = L'.sharp → L.s = L'.s → L.k = L'.k → rk ρ L.e = rk ρ L'.e := by
  first | exact @GlobalTheory.BadShare.CoDiag.rk_e_eq | exact GlobalTheory.BadShare.CoDiag.rk_e_eq | (intros; apply GlobalTheory.BadShare.CoDiag.rk_e_eq <;> assumption)
