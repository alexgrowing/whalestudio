import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommonResolutionPotentialComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.green_function_character_sum : ∀ (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ) (m k : ℕ) (S : F[X] → ℂ), 0 < m → ((Nat.card F : ℂ) ^ m - 1) * ∑ᶠ x, psiG (rootSum θ k) m x * star (chG S m x) = (Nat.card (GL (Fin m) F) : ℂ) * ∑ᶠ α ∈ {α : AlgebraicClosure F | α ^ (Nat.card F ^ m - 1) = 1}, θ α ^ k * star (S (minpoly F α ^ (m / (minpoly F α).natDegree))) := by
  first | (exact @GlobalTheory.Shin.psiG_rootSum_pair_chG_eq_sum_torus) | (exact GlobalTheory.Shin.psiG_rootSum_pair_chG_eq_sum_torus) | (intros; apply GlobalTheory.Shin.psiG_rootSum_pair_chG_eq_sum_torus  <;> assumption)
