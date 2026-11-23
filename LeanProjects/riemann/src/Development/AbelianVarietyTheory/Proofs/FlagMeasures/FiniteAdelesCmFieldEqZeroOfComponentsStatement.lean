import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteAdelesCmFieldEqZeroOfComponents
import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SerFixOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteCosetsHeckeSetAtSplitPlaceOutsideLevel
open NumberField IsDedekindDomain ReciprocityTheory.Aut
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteAdelesCmField_eq_zero_of_components : ∀ (L : Type) [Field L] [NumberField L] (a : ReciprocityTheory.Aut.AL L), (∀ v, ReciprocityTheory.Aut.compAt L v a = 0) → a = 0 := by
  first | exact @GlobalTheory.AL_eq_zero_of_compAt | exact GlobalTheory.AL_eq_zero_of_compAt | (intros; apply GlobalTheory.AL_eq_zero_of_compAt <;> assumption)
