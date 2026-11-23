import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HypercohomologyTrivialOfTermsDegreeZero
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HypercohomologyPullbackPushforwardFunctorialStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hypercohomology_trivial_of_terms_degreeZero : ∀ (R : Type) [CommRing R] (K M : Cx R) [K.IsStrictlyLE 0], (∀ p n : ℤ, p ≤ 0 → Subsingleton (CohomologyClass (sgl (K.X p)) M n)) → ∀ n : ℤ, Subsingleton (CohomologyClass K M n) := by
  first | exact @GlobalTheory.nullHtpy_stair | exact GlobalTheory.nullHtpy_stair | (intros; apply GlobalTheory.nullHtpy_stair <;> assumption)
