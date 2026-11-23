import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AlgebraicSubringClosureCommonDenominator
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModQPrin
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModJTau
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algebraic_subring_closure_common_denominator : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [Algebra.IsAlgebraic ℚ Ω] (S : Finset Ω), ∃ D : ℕ, 0 < D ∧ ∀ x ∈ Subring.closure (S : Set Ω), ∃ k : ℕ, IsIntegral ℤ ((D : Ω) ^ k * x) := by
  first | exact @GlobalTheory.finite_subring_common_denominator | exact GlobalTheory.finite_subring_common_denominator | (intros; apply GlobalTheory.finite_subring_common_denominator <;> assumption)
