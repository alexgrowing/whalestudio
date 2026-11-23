import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftLDegReg
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.deg_liftL_and_reg_pow : ∀ (q l : ℕ) (L : List (ℕ × ℕ)), 2 ≤ q → 0 < l → (∀ p ∈ L, 0 < p.1 ∧ l ∣ p.1 ∧ Reg q p.1 p.2) → deg (liftL q l L) = deg L ∧ ∀ p ∈ liftL q l L, 0 < p.1 ∧ Reg (q ^ l) p.1 p.2 := by
  first | (exact @GlobalTheory.Shin.liftL_deg_reg) | (exact GlobalTheory.Shin.liftL_deg_reg) | (intros; apply GlobalTheory.Shin.liftL_deg_reg  <;> assumption)
