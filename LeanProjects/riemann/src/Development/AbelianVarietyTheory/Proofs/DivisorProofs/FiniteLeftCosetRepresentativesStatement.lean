import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteLeftCosetRepresentatives
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_left_coset_representatives : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (r : ℕ), 0 < r → ∀ s : Gr G r, ∃ S : Finset (Gr G r), ∀ k ∈ KHT p G.m G.n r G.Fw, ∃ s' ∈ S, ∃ k' ∈ KHT p G.m G.n r G.Fw, k * s = s' * k' := by
  first | (exact @GlobalTheory.orbFin_KHT_cmd) | (exact GlobalTheory.orbFin_KHT_cmd) | (intros; apply GlobalTheory.orbFin_KHT_cmd <;> assumption)
