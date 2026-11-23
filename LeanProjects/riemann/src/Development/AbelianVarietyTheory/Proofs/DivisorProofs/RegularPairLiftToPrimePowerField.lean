import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlphaKernelDerivativeVanishes
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regular_pair_lift_to_prime_power_field : ∀ q l m k : ℕ, 2 ≤ q → l.Prime → 0 < m → ¬ l ∣ m → Reg q m k → Reg (q ^ l) m (k * ∑ i ∈ Finset.range l, q ^ (m * i)) ∧ ∃ a, (k * ∑ i ∈ Finset.range l, q ^ (m * i)) * q ≡ (k * ∑ i ∈ Finset.range l, q ^ (m * i)) * (q ^ l) ^ a [MOD (q ^ l) ^ m - 1] := by
  first | (exact @GlobalTheory.Shin.reg_norm_frob) | (exact GlobalTheory.Shin.reg_norm_frob) | (intros; apply GlobalTheory.Shin.reg_norm_frob  <;> assumption)
