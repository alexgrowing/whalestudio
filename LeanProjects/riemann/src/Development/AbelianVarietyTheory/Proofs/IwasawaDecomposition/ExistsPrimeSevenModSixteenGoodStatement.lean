import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPrimeSevenModSixteenGood
import Formalism.GL3MeanSquares.PrimeCountAsymptoticInProgressions
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Formalism.CyclotomicNorms.StatementI
import Development.AbelianVarietyTheory.Definitions.Foundations.RayPrimes
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExplZeta
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExplChi
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LogDerOne
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ZeroCount
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.IsExcRat
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.PageThm
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Jutila
open Finset ArithmeticFunction NumberField IsDedekindDomain Filter Topology GlobalTheory.Mem.An Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab
open scoped nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_prime_seven_mod_sixteen_good : GlobalTheory.Mem.An.ExplZeta → GlobalTheory.Mem.An.ExplChi → GlobalTheory.Mem.An.LogDerOne → GlobalTheory.Mem.An.ZeroCount → Formalism.ZeroFreeDirichlet.ZFRDirichlet → GlobalTheory.Mem.An.TZRat → GlobalTheory.Mem.An.PageThm → GlobalTheory.Mem.An.Jutila → ∀ eps : ℝ, 0 < eps → eps < 1 / 52 → ∃ x₀ C : ℝ, 0 < C ∧ ∀ x : ℝ, x₀ ≤ x → ∀ q : ℕ, q.Prime → q % 8 = 3 → Real.sqrt (GlobalTheoryTheory.X1 x eps) < q → (q : ℝ) ≤ GlobalTheoryTheory.X1 x eps → ∃ d : ℕ, d.Prime ∧ d % 16 = 7 ∧ Real.sqrt (GlobalTheoryTheory.X2 x eps) < d ∧ (d : ℝ) ≤ GlobalTheoryTheory.X2 x eps ∧ GlobalTheoryTheory.kronSym (-(d : ℤ)) q = 1 ∧ (∀ p : ℕ, p.Prime → (p : ℝ) ≤ x ^ (eps / 5) → GlobalTheoryTheory.kronSym (-(d : ℤ)) p = 1) ∧ (∀ i k : Fin 2, GoodAllFor (8 * GlobalTheoryTheory.X1 x eps * GlobalTheoryTheory.X2 x eps) (fun a => GlobalTheoryTheory.chi8 a ^ k.1 * GlobalTheoryTheory.chDir d a * GlobalTheoryTheory.psDir q a ^ i.1) (8 * q * d)) ∧ BoundsAtX x eps C (GlobalTheoryTheory.chDir d) (8 * q * d) ∧ BoundsAtX x eps C (fun a => GlobalTheoryTheory.chDir d a * GlobalTheoryTheory.psDir q a) (8 * q * d) := by
  first | exact @GlobalTheory.SplitPrimeChoice.exists_prime_split_good_bounds | exact GlobalTheory.SplitPrimeChoice.exists_prime_split_good_bounds | (intros; apply GlobalTheory.SplitPrimeChoice.exists_prime_split_good_bounds <;> assumption)
