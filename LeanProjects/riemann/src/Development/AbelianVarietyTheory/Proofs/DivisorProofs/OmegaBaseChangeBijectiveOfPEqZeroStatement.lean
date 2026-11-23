import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OmegaBaseChangeBijectiveOfPEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigOfOmegaInjectiveOfEqZero
open TensorProduct Coalgebra Bialgebra CategoryTheory WithConv GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.omega_baseChange_bijective_of_p_eq_zero : ∀ {p : ℕ} {R : Type} [CommRing R] (G : PDivGroup p R) (R' : Type) [CommRing R'] [Algebra R R'], (p : R) = 0 → Function.Bijective (liftSemi (G.toBase R').omega) := by
  first | exact @GlobalTheory.PDivGroup.omega_baseChange_bijective | exact GlobalTheory.PDivGroup.omega_baseChange_bijective | (intros; apply GlobalTheory.PDivGroup.omega_baseChange_bijective <;> assumption)
