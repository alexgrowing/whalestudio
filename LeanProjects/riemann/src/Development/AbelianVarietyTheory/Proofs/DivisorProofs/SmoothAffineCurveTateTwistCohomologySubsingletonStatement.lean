import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothAffineCurveTateTwistCohomologySubsingleton
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smoothAffineCurve_tateTwistCohomology_subsingleton_of_ge_three : ∀ (q : ℕ) [NeZero q] (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B], IsUnit (q : k) → ∀ n i : ℤ, 3 ≤ n → Subsingleton (Ht q (sp B) n i) := by
  first | (exact @GlobalTheory.EtC.AffineCurve.subsingleton_of_three_le) | (exact GlobalTheory.EtC.AffineCurve.subsingleton_of_three_le) | (intros; apply GlobalTheory.EtC.AffineCurve.subsingleton_of_three_le <;> assumption)
