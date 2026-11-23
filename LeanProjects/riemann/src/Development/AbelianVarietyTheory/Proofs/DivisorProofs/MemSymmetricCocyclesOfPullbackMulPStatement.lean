import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSymmetricCocyclesOfPullbackMulP
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigOfOmegaInjectiveOfEqZero
open TensorProduct Coalgebra Bialgebra CategoryTheory WithConv GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_symmetricCocycles_of_pullback_mulP : ∀ {p : ℕ} {R : Type} [CommRing R] (G : PDivGroup p R) (n : ℕ) (c : G.A n ⊗[R] G.A n), pullbackTwo (G.mulP n) c ∈ symCocycles R (G.A (n + 1)) → c ∈ symCocycles R (G.A n) := by
  first | exact @GlobalTheory.PDivGroup.mem_symCocycles_of_pullTwo_mulP | exact GlobalTheory.PDivGroup.mem_symCocycles_of_pullTwo_mulP | (intros; apply GlobalTheory.PDivGroup.mem_symCocycles_of_pullTwo_mulP <;> assumption)
