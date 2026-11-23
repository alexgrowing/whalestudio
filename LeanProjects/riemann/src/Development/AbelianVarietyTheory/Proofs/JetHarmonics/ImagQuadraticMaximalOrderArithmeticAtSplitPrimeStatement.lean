import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ImagQuadraticMaximalOrderArithmeticAtSplitPrime
import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.imagQuadraticMaximalOrder_arithmetic_at_split_prime : ∀ (d q : ℕ) [Fact q.Prime] (ι : ℂ ≃+* ℂ_[q]), d.Prime → d % 16 = 7 → Split d q → (InOK d 1 ∧ InOK d (wK d) ∧ ∀ α β, InOK d α → InOK d β → InOK d (α + β) ∧ InOK d (α * β) ∧ InOK d (-α) ∧ InOK d (conj α)) ∧ (∀ α, InOK d α → (∃ a : ℤ_[q], ι α = zc a) ∧ (∃ N : ℕ, (N : ℂ) = α * conj α) ∧ α ∈ algebraicClosure ℚ ℂ) ∧ (∀ (α : ℂ) (n : ℕ), InOK d α → ‖ι α‖ ≤ (q : ℝ) ^ (-(n : ℤ)) → ‖ι (conj α)‖ ≤ (q : ℝ) ^ (-(n : ℤ)) → InOK d (α / (q : ℂ) ^ n)) ∧ (∀ m s : ℕ, Nat.Coprime s q → ∃ e, InOK d e ∧ ‖ι ((s : ℂ) * e) - 1‖ ≤ (q : ℝ) ^ (-(m : ℤ)) ∧ ‖ι (conj e)‖ ≤ (q : ℝ) ^ (-(m : ℤ))) ∧ (∀ n : ℕ, ∃ α, InOK d α ∧ ‖ι α‖ ≤ (q : ℝ) ^ (-(n : ℤ)) ∧ ¬ InOK d (α / 2)) ∧ (∀ x y, InOK d x → InOK d y → ∃ k : ℤ, (h1 d x y).im = k) ∧ ¬ q ∣ d := by
  first | exact @GlobalTheory.MomOne.okArith | exact GlobalTheory.MomOne.okArith | (intros; apply GlobalTheory.MomOne.okArith <;> assumption)
