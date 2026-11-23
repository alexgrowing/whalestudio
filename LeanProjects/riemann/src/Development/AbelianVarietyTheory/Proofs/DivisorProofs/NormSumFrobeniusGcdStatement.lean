import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormSumFrobeniusGcd
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusPowRootOfUnity
open ReciprocityTheory.DiscreteGroups.LocalClassField GlobalTheory.LKRes GlobalTheory.LKRes.ResSplit
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_sum_frobenius_gcd : ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)), FiniteDimensional ℚ_[p] K → ∀ (f r : ℕ), qK p K = p ^ f → 0 < r → ∀ (ζ : PadicAlgCl p), ζ ^ (p ^ r - 1) = 1 → ∀ (c : Fin r → K) (s : ℕ), ∃ i < Nat.gcd f r, ‖∑ j : Fin r, (c j : PadicAlgCl p) * (ζ ^ p ^ s) ^ (j : ℕ)‖ = ‖∑ j : Fin r, (c j : PadicAlgCl p) * (ζ ^ p ^ i) ^ (j : ℕ)‖ := by
  first | exact @GlobalTheory.LKRes.ResSplit.spread | exact GlobalTheory.LKRes.ResSplit.spread | (intros; apply GlobalTheory.LKRes.ResSplit.spread <;> assumption)
