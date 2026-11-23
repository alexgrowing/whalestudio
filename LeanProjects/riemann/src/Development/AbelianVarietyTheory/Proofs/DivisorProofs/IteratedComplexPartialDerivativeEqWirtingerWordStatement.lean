import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IteratedComplexPartialDerivativeEqWirtingerWord
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableRisingS
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.WeightTwoSum
open scoped ContDiff nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iteratedComplexPartialDerivative_eq_wirtingerWord : ∀ (I : Type) [Fintype I] [DecidableEq I] (U : Set (I → ℂ)) (g : (I → ℂ) → ℂ), IsOpen U → DifferentiableOn ℂ g U → ∀ (l : List I), ∀ z ∈ U, iterD l g z = wirtWord (l.map fun i => (i, false)) g z := by
  first | exact @GlobalTheory.HoloWirt.iterD_eq_wirtWord | exact GlobalTheory.HoloWirt.iterD_eq_wirtWord | (intros; apply GlobalTheory.HoloWirt.iterD_eq_wirtWord <;> assumption)
