import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RankinConvolutionCoeffStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LseriesSummableTwistPowOfSqSummableStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LseriesShiftTwistStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LSeriesSummableBoundedMulOfSummableNormSqStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LSeriesSummableMulDivisorSumStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LseriesSquaresEqStatement
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

theorem rankin_dirichlet_identity : ∀ (e : ℕ) (χ ψ θ g : ℕ → ℂ) (s : ℝ), 1 ≤ e → 0 < s → (∀ m n, ψ (m * n) = ψ m * ψ n) → (∀ m n, θ (m * n) = θ m * θ n) → (∀ n, ‖χ n‖ ≤ 1 ∧ ‖ψ n‖ ≤ 1 ∧ ‖θ n‖ ≤ 1) → (∀ m n : ℕ, 0 < m → 0 < n → g m * g n = ∑ δ ∈ (Nat.gcd m n).divisors, χ δ * (δ : ℂ) ^ (2 * e) * g (m * n / δ ^ 2)) → (∀ t : ℝ, 0 < t → Summable fun n : ℕ => ‖g n‖ ^ 2 / (n : ℝ) ^ (((2 * e + 1 : ℕ) : ℝ) + t)) → ∀ b : ℕ → ℂ, (∀ n, n ≠ 0 → b n = ∑ p ∈ n.divisorsAntidiagonal, ψ p.1 * (p.1 : ℂ) ^ (e - 1) * θ p.2) → LSeriesSummable (fun n => g n * b n) ((2 * (e : ℝ) + s : ℝ) : ℂ) ∧ LSeries (fun n => χ n * ψ n * θ n) ((e + 1 : ℕ) + 2 * s) * LSeries (fun n => g n * b n) ((2 * (e : ℝ) + s : ℝ) : ℂ) = LSeries (fun n => ψ n * g n) ((e + 1 : ℝ) + s : ℝ) * LSeries (fun n => θ n * g n) ((2 * (e : ℝ) + s : ℝ) : ℂ) := by
  intro e χ ψ θ g s he hs hψ hθ hn hg hsum b hb
  have hGB := GlobalTheory.T.lSeriesSummable_mul_divisorSum' e ψ θ g b s he hs (fun n => ⟨(hn n).2.1, (hn n).2.2⟩) hsum hb
  have hU := GlobalTheory.T.lSeriesSummable_twist_pow_of_summable_sq_div e ψ g s he hs (fun n => (hn n).2.1) hsum
  have hV := GlobalTheory.T.lSeriesSummable_bounded_mul_of_summable_sq_div e θ g s he hs (fun n => (hn n).2.2) hsum
  have hz := GlobalTheory.T.lSeries_squares_eq_shift e χ ψ θ s he hs hn
  refine ⟨hGB, ?_⟩
  rw [← hz.2, ← LSeries_convolution' hz.1 hGB, ← GlobalTheory.T.lSeries_twist_natPow_eq_shift e ψ g s he, ← LSeries_convolution' hU hV]
  exact LSeries_congr (fun {n} hn0 => (GlobalTheory.T.convolution_twist_eq_convolution_squares e χ ψ θ g b hψ hθ hg hb n hn0).symm) _

end GlobalTheory.EisM
