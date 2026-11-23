import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DirichletLZeroSymmetry
import Formalism.GL3MeanSquares.PrimeCountAsymptoticInProgressions
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Formalism.CyclotomicNorms.StatementI
import Development.AbelianVarietyTheory.Definitions.Foundations.RayPrimes
open Finset ArithmeticFunction NumberField IsDedekindDomain Filter Topology GlobalTheory.Mem.An Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab
open scoped nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dirichlet_L_zero_symmetry : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive → ∀ ρ : ℂ, 0 < ρ.re → ρ.re < 1 → ((DirichletCharacter.LFunction χ ρ = 0 ↔ DirichletCharacter.LFunction χ⁻¹ (1 - ρ) = 0) ∧ zmult χ ρ = zmult χ⁻¹ (1 - ρ)) := by
  first | exact @GlobalTheory.Mem.An.zeros_symm_one_sub | exact GlobalTheory.Mem.An.zeros_symm_one_sub | (intros; apply GlobalTheory.Mem.An.zeros_symm_one_sub <;> assumption)
