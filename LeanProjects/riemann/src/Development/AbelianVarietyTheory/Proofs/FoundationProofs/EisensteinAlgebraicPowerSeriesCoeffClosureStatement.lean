import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EisensteinAlgebraicPowerSeriesCoeffClosure
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModQPrin
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModJTau
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eisenstein_algebraic_powerSeries_coeff_closure : ∀ (L : Type) [Field L] [CharZero L] (A : Subring L) (b : PowerSeries L) (Q : Polynomial (PowerSeries L)), Q ≠ 0 → (∀ i k, PowerSeries.coeff k (Q.coeff i) ∈ A) → Q.eval b = 0 → ∃ S : Finset L, ∀ k, PowerSeries.coeff k b ∈ Subring.closure ((A : Set L) ∪ S) := by
  first | exact @GlobalTheory.AlgPowerSeries.exists_finset_coeff_mem_closure | exact GlobalTheory.AlgPowerSeries.exists_finset_coeff_mem_closure | (intros; apply GlobalTheory.AlgPowerSeries.exists_finset_coeff_mem_closure <;> assumption)
