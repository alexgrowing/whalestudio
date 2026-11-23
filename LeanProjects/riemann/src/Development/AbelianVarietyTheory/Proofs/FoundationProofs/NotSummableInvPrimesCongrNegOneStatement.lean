import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NotSummableInvPrimesCongrNegOne
import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.not_summable_inv_primes_congr_neg_one : ∀ M : ℕ, 0 < M → ¬ Summable fun p : ℕ => if p.Prime ∧ (p : ZMod M) = -1 then (1 : ℝ) / p else 0 := by
  first | exact @GlobalTheory.not_summable_one_div_primes_eq_neg_one | exact GlobalTheory.not_summable_one_div_primes_eq_neg_one | (intros; apply GlobalTheory.not_summable_one_div_primes_eq_neg_one <;> assumption)
