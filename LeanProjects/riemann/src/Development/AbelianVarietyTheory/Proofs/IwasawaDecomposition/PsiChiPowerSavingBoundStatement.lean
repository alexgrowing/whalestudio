import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PsiChiPowerSavingBound
import Formalism.GL3MeanSquares.PrimeCountAsymptoticInProgressions
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Formalism.CyclotomicNorms.StatementI
import Development.AbelianVarietyTheory.Definitions.Foundations.RayPrimes
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExplChi
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LogDerOne
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ZeroCount
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExplZeta
open Finset ArithmeticFunction NumberField IsDedekindDomain Filter Topology GlobalTheory.Mem.An Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab
open scoped nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.psi_chi_power_saving_bound : GlobalTheory.Mem.An.ExplChi → GlobalTheory.Mem.An.LogDerOne → GlobalTheory.Mem.An.ZeroCount → Formalism.ZeroFreeDirichlet.ZFRDirichlet → GlobalTheory.Mem.An.ExplZeta → ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ (Q : ℝ) (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), 3 ≤ Q → χ ≠ 1 → GlobalTheoryTheory.GoodFor Q χ → ∀ u : ℝ, 2 ≤ u → ‖psiChi χ u‖ ≤ C₁ * (u ^ (1 - (1 : ℝ) / 400) * Real.log (u * Q) ^ 2 + u / Q * Real.log (u * Q) ^ 2) := by
  first | exact @GlobalTheory.Mem.An.GoodBound.psiChi_bound_of_goodFor | exact GlobalTheory.Mem.An.GoodBound.psiChi_bound_of_goodFor | (intros; apply GlobalTheory.Mem.An.GoodBound.psiChi_bound_of_goodFor <;> assumption)
