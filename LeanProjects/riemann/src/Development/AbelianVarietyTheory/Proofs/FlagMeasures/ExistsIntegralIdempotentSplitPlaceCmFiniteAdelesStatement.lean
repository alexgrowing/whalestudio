import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIntegralIdempotentSplitPlaceCmFiniteAdeles
import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SerFixOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteCosetsHeckeSetAtSplitPlaceOutsideLevel
open NumberField IsDedekindDomain ReciprocityTheory.Aut
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integralIdempotent_splitPlace_cmFiniteAdeles : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (s : ReciprocityTheory.Aut.SplitPlace L), ∃ ε : ReciprocityTheory.Aut.AL L, ε * ε = ε ∧ ε * ReciprocityTheory.Aut.conjAL L ε = 0 ∧ ε ∈ ReciprocityTheory.Aut.ALint L ∧ s.proj ε = 1 ∧ ReciprocityTheory.Aut.compAt L s.v (ε + ReciprocityTheory.Aut.conjAL L ε) = 1 ∧ ∀ v, v ≠ s.v → ReciprocityTheory.Aut.compAt L v ε = 0 ∧ ReciprocityTheory.Aut.compAt L v (ReciprocityTheory.Aut.conjAL L ε) = 0 := by
  first | exact @GlobalTheory.SplitIdem.exists_idem | exact GlobalTheory.SplitIdem.exists_idem | (intros; apply GlobalTheory.SplitIdem.exists_idem <;> assumption)
