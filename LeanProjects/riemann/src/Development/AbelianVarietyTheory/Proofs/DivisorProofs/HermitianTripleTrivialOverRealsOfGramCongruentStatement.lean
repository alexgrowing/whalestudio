import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianTripleTrivialOverRealsOfGramCongruent
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianTriple_trivial_over_reals_of_gram_congruent : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (β : G.Cˣ), (∀ v : InfinitePlace G.F, ∃ W : GL (Fin G.n) ℂ, G.gram v * G.psi v ((β⁻¹ : G.Cˣ) : G.C) = (W : Matrix (Fin G.n) (Fin G.n) ℂ)ᴴ * G.gram v * (W : Matrix (Fin G.n) (Fin G.n) ℂ)) → ∃ z : (ℝ ⊗[ℚ] G.C)ˣ, Triv G ℝ β z 1 := by
  first | (exact @GlobalTheory.LKMid.trivR_of_gram_psi_inv_congr) | (exact GlobalTheory.LKMid.trivR_of_gram_psi_inv_congr) | (intros; apply GlobalTheory.LKMid.trivR_of_gram_psi_inv_congr  <;> assumption)
