import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefficientsBoundedRootsUnity
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusPowRootOfUnity
open ReciprocityTheory.DiscreteGroups.LocalClassField GlobalTheory.LKRes GlobalTheory.LKRes.ResSplit
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coefficients_bounded_roots_unity : ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ), ¬ p ∣ N → ∀ (w : Fin r → PadicAlgCl p), (∀ s, w s ^ N = 1) → Function.Injective w → ∀ (c : Fin r → PadicAlgCl p), (∀ s, ‖∑ j : Fin r, c j * w s ^ (j : ℕ)‖ ≤ 1) → ∀ j, ‖c j‖ ≤ 1 := by
  first | exact @GlobalTheory.LKRes.ResSplit.vandermonde_integral_of_roots_of_unity | exact GlobalTheory.LKRes.ResSplit.vandermonde_integral_of_roots_of_unity | (intros; apply GlobalTheory.LKRes.ResSplit.vandermonde_integral_of_roots_of_unity <;> assumption)
