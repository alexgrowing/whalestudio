import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaDieudonneModFrobeniusDifferentials
import Development.AbelianVarietyTheory.Definitions.Divisors.RedSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerEqRangeOfRangeEqKer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_theta_dieudonne_mod_frobenius_differentials : ∀ (p : ℕ) [Fact p.Prime] (T : Theory p) (k : Type) [Field k] [CharP k p] [PerfectRing k p], ∃ θ : ∀ G : PDivGroup p k, T.M G →+ G.omega, ∀ G : PDivGroup p k, (∀ m, G.rigOfOmega (θ G m) = T.red G (T.V G m)) ∧ Function.Surjective (θ G) ∧ (∀ m, θ G m = 0 ↔ ∃ n, m = T.F G n) ∧ (∀ (a : (WittVector p k)) m, θ G (WittVector.frobenius a • m) = WittVector.constantCoeff a • θ G m) ∧ ∀ (H : PDivGroup p k) (f : G ⟶ H) (m : T.M H), θ G (T.map f m) = omegaMap G H f (θ H m) := by
  first | exact @GlobalTheory.Dieu.theta_exists | exact GlobalTheory.Dieu.theta_exists | (intros; apply GlobalTheory.Dieu.theta_exists <;> assumption)
