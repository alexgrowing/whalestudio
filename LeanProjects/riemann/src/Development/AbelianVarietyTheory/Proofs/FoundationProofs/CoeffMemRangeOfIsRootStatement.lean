import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoeffMemRangeOfIsRoot
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModQPrin
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModJTau
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeff_mem_range_of_isRoot_of_coeff_mem_range : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (ε : Ω →+* ℂ) (b : PowerSeries ℂ) (Q : Polynomial (PowerSeries ℂ)), Q ≠ 0 → (∀ i k, PowerSeries.coeff k (Q.coeff i) ∈ ε.range) → Q.eval b = 0 → ∀ k, PowerSeries.coeff k b ∈ ε.range := by
  first | exact @GlobalTheory.PsRoot.coeff_mem_range_of_isRoot | exact GlobalTheory.PsRoot.coeff_mem_range_of_isRoot | (intros; apply GlobalTheory.PsRoot.coeff_mem_range_of_isRoot <;> assumption)
