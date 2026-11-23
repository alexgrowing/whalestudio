import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RayClassNumberBounds
import Formalism.GL3MeanSquares.PrimeCountAsymptoticInProgressions
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Formalism.CyclotomicNorms.StatementI
import Development.AbelianVarietyTheory.Definitions.Foundations.RayPrimes
open Finset ArithmeticFunction NumberField IsDedekindDomain Filter Topology GlobalTheory.Mem.An Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab
open scoped nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ray_class_number_bounds : ∀ (K : Type) [Field K] [NumberField K] (𝔮 : Ideal (𝓞 K)), 𝔮 ≠ ⊥ → 1 ≤ rayNo 𝔮 ∧ rayNo 𝔮 ≤ classNumber K * Ideal.absNorm 𝔮 ∧ rayP 𝔮 ≤ rayI 𝔮 := by
  first | exact @GlobalTheory.Mem.RayNo.rayNo_bounds | exact GlobalTheory.Mem.RayNo.rayNo_bounds | (intros; apply GlobalTheory.Mem.RayNo.rayNo_bounds <;> assumption)
