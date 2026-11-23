import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericIntersectionEqualsPointsIntegral
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MinpolyIrreducibleNatDegreeOfRankOne
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.embeddings_real_independent : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (k : ℕ) (e : Fin k → G.C), LinearIndependent ℚ e → LinearIndependent ℝ (fun j => (fun w i l => G.psi w (e j) i l : InfinitePlace G.F → Fin G.n → Fin G.n → ℂ)) := by
  first | (exact @GlobalTheory.LKCx.psi_linearIndependent_real) | (exact GlobalTheory.LKCx.psi_linearIndependent_real) | (intros; apply GlobalTheory.LKCx.psi_linearIndependent_real  <;> assumption)
