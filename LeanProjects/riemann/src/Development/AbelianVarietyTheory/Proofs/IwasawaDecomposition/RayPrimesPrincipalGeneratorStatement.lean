import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RayPrimesPrincipalGenerator
import Formalism.GL3MeanSquares.PrimeCountAsymptoticInProgressions
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Formalism.CyclotomicNorms.StatementI
import Development.AbelianVarietyTheory.Definitions.Foundations.RayPrimes
open Finset ArithmeticFunction NumberField IsDedekindDomain Filter Topology GlobalTheory.Mem.An Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab
open scoped nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ray_primes_principal_generator : ∀ (K : Type) [Field K] [NumberField K] (𝔮 : Ideal (𝓞 K)), 𝔮 ≠ ⊥ → ∀ (X : ℝ), ∀ v ∈ rayPrimes 𝔮 X, ∃ π : 𝓞 K, v.asIdeal = Ideal.span {π} ∧ π - 1 ∈ 𝔮 := by
  first | exact @GlobalTheory.Mem.An.exists_generator_of_mem_rayPrimes | exact GlobalTheory.Mem.An.exists_generator_of_mem_rayPrimes | (intros; apply GlobalTheory.Mem.An.exists_generator_of_mem_rayPrimes <;> assumption)
