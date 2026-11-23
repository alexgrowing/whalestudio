import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArtinSchreierCocycleRoot
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.psi_sum_eq_char_sum_against_cusp_form : ∀ (F : Type) [Field F] [Finite F], ∀ (θ : AlgebraicClosure F →* ℂ) (S : F[X] → ℂ) (n k : ℕ), S 1 = 0 → ∑ᶠ x, psiG S n x * star (cusp θ n k x) = ∑ᶠ x, chG S n x * star (cusp θ n k x) := by
  first | (exact @GlobalTheory.Shin.sum_psiG_mul_star_cusp_eq) | (exact GlobalTheory.Shin.sum_psiG_mul_star_cusp_eq) | (intros; apply GlobalTheory.Shin.sum_psiG_mul_star_cusp_eq  <;> assumption)
