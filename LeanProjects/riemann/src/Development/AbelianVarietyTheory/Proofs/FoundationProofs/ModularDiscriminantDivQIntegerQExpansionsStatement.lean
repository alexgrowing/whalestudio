import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularDiscriminantDivQIntegerQExpansions
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModQPrin
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModJTau
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.modularDiscriminant_div_q_integer_qExpansions : (∃ c : ℕ → ℤ, c 0 = 1 ∧ HasQ 1 (fun τ => DD τ / Complex.exp (2 * Real.pi * Complex.I * τ)) fun n => (c n : ℂ)) ∧ ∃ c : ℕ → ℤ, c 0 = 1 ∧ HasQ 1 (fun τ => Complex.exp (2 * Real.pi * Complex.I * τ) / DD τ) fun n => (c n : ℂ) := by
  first | exact @GlobalTheory.FN.dd_div_q_and_q_div_dd | exact GlobalTheory.FN.dd_div_q_and_q_div_dd | (intros; apply GlobalTheory.FN.dd_div_q_and_q_div_dd <;> assumption)
