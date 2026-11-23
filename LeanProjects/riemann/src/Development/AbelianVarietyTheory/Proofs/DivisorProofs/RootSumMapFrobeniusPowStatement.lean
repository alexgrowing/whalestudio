import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RootSumMapFrobeniusPow
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rootSum_map_frobenius_pow_eq_rootSum_mul : ∀ (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ) (t : F →+* F) (j : ℕ), (∀ x, t x = x ^ (ringChar F ^ j)) → ∀ (k : ℕ) (P : F[X]), rootSum θ k (P.map t) = rootSum θ (k * ringChar F ^ j) P := by
  first | (exact @GlobalTheory.Shin.rootSum_map_frobeniusPow) | (exact GlobalTheory.Shin.rootSum_map_frobeniusPow) | (intros; apply GlobalTheory.Shin.rootSum_map_frobeniusPow  <;> assumption)
