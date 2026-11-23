import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GChiApproximationSum
import Formalism.GL3MeanSquares.PrimeCountAsymptoticInProgressions
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Formalism.CyclotomicNorms.StatementI
import Development.AbelianVarietyTheory.Definitions.Foundations.RayPrimes
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExplZeta
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExplChi
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LogDerOne
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ZeroCount
open Finset ArithmeticFunction NumberField IsDedekindDomain Filter Topology GlobalTheory.Mem.An Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab
open scoped nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.g_chi_approximation_sum : GlobalTheory.Mem.An.ExplZeta → GlobalTheory.Mem.An.ExplChi → GlobalTheory.Mem.An.LogDerOne → GlobalTheory.Mem.An.ZeroCount → Formalism.ZeroFreeDirichlet.ZFRDirichlet → ∀ eps : ℝ, 0 < eps → eps < 1 / 52 → ∃ x₀ C : ℝ, 0 < C ∧ ∀ x : ℝ, x₀ ≤ x → ∀ (Q : ℝ) (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), 0 < Q → x ^ (eps / 6) ≤ Real.log Q → Real.log Q ≤ x ^ (eps / 4) → χ ≠ 1 → GlobalTheoryTheory.GoodFor Q χ → ‖GlobalTheoryTheory.gChi χ x + ∑ n ∈ Icc 1 ⌊x ^ (400 : ℝ)⌋₊, (GlobalTheoryTheory.cn x n : ℂ) * χ (n : ZMod q)‖ ≤ x ^ eps ∧ ‖GlobalTheoryTheory.logDerivativeAtOne χ‖ ≤ C * Real.log x := by
  first | exact @GlobalTheory.GoodCharacterSum.gChi_add_sum_bound | exact GlobalTheory.GoodCharacterSum.gChi_add_sum_bound | (intros; apply GlobalTheory.GoodCharacterSum.gChi_add_sum_bound <;> assumption)
