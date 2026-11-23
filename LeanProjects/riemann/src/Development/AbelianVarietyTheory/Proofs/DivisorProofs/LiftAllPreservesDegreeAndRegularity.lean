import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFormalGermOpenAffine
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lift_all_preserves_degree_and_regularity : ∀ (q l : ℕ) (L : List (ℕ × ℕ)), 2 ≤ q → l.Prime → (∀ p ∈ L, 0 < p.1 ∧ Reg q p.1 p.2) → deg (liftAll q l L) = deg L ∧ ∀ p ∈ liftAll q l L, 0 < p.1 ∧ Reg (q ^ l) p.1 p.2 := by
  first | (exact @GlobalTheory.liftAll_deg_reg) | (exact GlobalTheory.liftAll_deg_reg) | (intros; apply GlobalTheory.liftAll_deg_reg <;> assumption)
