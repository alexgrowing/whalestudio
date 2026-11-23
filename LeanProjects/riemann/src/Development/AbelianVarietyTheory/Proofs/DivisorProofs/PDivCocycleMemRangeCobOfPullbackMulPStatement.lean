import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivCocycleMemRangeCobOfPullbackMulP
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigOfOmegaInjectiveOfEqZero
open TensorProduct Coalgebra Bialgebra CategoryTheory WithConv GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pDivCocycle_mem_range_cob_of_pullback_mulP : ∀ {p : ℕ} [Fact p.Prime] {R : Type} [CommRing R] (G : PDivGroup p R) (c : G.cocycles) (B : G.funs), G.cob B = cocyclesMap ((p : ℤ_[p]) • 𝟙 G) c → B.1 1 = 0 → c ∈ LinearMap.range G.cob := by
  first | exact @GlobalTheory.cocycle_mem_range_cob_of_pullback_mulP | exact GlobalTheory.cocycle_mem_range_cob_of_pullback_mulP | (intros; apply GlobalTheory.cocycle_mem_range_cob_of_pullback_mulP <;> assumption)
