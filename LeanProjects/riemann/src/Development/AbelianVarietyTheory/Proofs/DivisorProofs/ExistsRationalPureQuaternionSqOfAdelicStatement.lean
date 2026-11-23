import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalPureQuaternionSqOfAdelic
import Development.AbelianVarietyTheory.Definitions.Divisors.OneMemH0WeightZero
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.QSA GlobalTheory.Published
open Matrix
open scoped Quaternion Topology TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rational_pure_quaternion_sq_of_adelic : ∀ (F : Type) [Field F] [NumberField F] (a b : F), a ≠ 0 → b ≠ 0 → ∀ c : F, c ≠ 0 → ∀ q : DA F a b, q.re = 0 → q * q = algebraMap (AF F) (DA F a b) (algebraMap F (AF F) c) → ∃ p : ℍ[F, a, b], p.re = 0 ∧ p * p = algebraMap F ℍ[F, a, b] c := by
  first | exact @GlobalTheory.QSA.PureSq.exists_rat_of_adelic | exact GlobalTheory.QSA.PureSq.exists_rat_of_adelic | (intros; apply GlobalTheory.QSA.PureSq.exists_rat_of_adelic <;> assumption)
