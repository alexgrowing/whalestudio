import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HassePrincipleNormTrace
import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PlaneSupports.PlaneSupp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianPlaneStrongApprox
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published GlobalTheory.CompanionTheory.PlaneSA Topology
open scoped TensorProduct Quaternion
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasse_principle_norm_trace : ∀ {F : Type} [Field F] [NumberField F] (d β t : F), (∀ x : Q d β F, qn x = 0 → x = 0) →
  (∀ u : Pl F, (∀ x : Q d β (Kp u), qn x = 0 → x = 0) →
    ∀ r : Kp u, r ^ 2 ≠ algebraMap F (Kp u) (t ^ 2 - 4)) →
  ∃ x : Q d β F, qn x = 1 ∧ 2 * x.re = t := by
  first | exact @GlobalTheory.CompanionTheory.PlaneSA.GlobalTrace.exists_qn_eq_one_two_mul_re | exact GlobalTheory.CompanionTheory.PlaneSA.GlobalTrace.exists_qn_eq_one_two_mul_re | (intros; apply GlobalTheory.CompanionTheory.PlaneSA.GlobalTrace.exists_qn_eq_one_two_mul_re <;> assumption)
