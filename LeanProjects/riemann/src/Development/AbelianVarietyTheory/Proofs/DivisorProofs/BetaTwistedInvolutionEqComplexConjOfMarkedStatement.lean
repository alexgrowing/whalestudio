import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BetaTwistedInvolutionEqComplexConjOfMarked
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowMemConj
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.StabFin
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.betaTwistedInvolution_eq_complexConj_of_marked : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P : Pair G) (μ : ℂ), G.a = 1 → P.Mark μ → ∀ (τ : FM P →+* ℂ) (a : FM P), τ (iM P a) = (starRingEnd ℂ) (τ a) := by
  first | (exact @GlobalTheory.StabFin.iM_conj) | (exact GlobalTheory.StabFin.iM_conj) | (intros; apply GlobalTheory.StabFin.iM_conj  <;> assumption)
