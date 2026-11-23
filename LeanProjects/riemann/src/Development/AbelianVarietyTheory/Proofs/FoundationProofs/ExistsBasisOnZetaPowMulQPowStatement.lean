import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsBasisOnZetaPowMulQPow
import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
open GlobalTheory.K5
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_basis_On_zeta_pow_mul_q_pow : ∀ (p : ℕ) [Fact p.Prime] (n : ℕ), ∃ b : Module.Basis (Fin (Nat.totient (p ^ n)) × Fin (p ^ n)) (O0 p) (On p n),
  ∀ i j, b (i, j) = xn p n ^ (i : ℕ) * yn p n ^ (j : ℕ) := by
  first | exact @GlobalTheory.K5.OnFree.on_free | exact GlobalTheory.K5.OnFree.on_free | (intros; apply GlobalTheory.K5.OnFree.on_free <;> assumption)
