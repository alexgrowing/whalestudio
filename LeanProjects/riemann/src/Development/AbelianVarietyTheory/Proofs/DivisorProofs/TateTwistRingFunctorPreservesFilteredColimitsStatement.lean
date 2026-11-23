import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistRingFunctorPreservesFilteredColimits
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tateTwistRingFunctor_preservesFilteredColimits : ∀ (q : ℕ) (i : ℤ), PreservesFilteredColimitsOfSize.{0, 0} (twF q i) := by
  first | (exact @GlobalTheory.EtC.TwistFiltered.twF_preservesFilteredColimits) | (exact GlobalTheory.EtC.TwistFiltered.twF_preservesFilteredColimits) | (intros; apply GlobalTheory.EtC.TwistFiltered.twF_preservesFilteredColimits  <;> assumption)
