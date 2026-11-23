import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PlaneApproxOfQuaternionApprox
import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PlaneSupports.PlaneSupp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianPlaneStrongApprox
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published GlobalTheory.CompanionTheory.PlaneSA Topology
open scoped TensorProduct Quaternion
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.plane_approx_of_quaternion_approx : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
  IsCMExt F E σ → ∀ β : F, β ≠ 0 → ∀ d : F, (∀ r : F, r ^ 2 ≠ d) → ∀ ξ : E, ξ ^ 2 = algebraMap F E d → σ ξ = -ξ →
  (∀ s : Pl F, (∃ x : Q d β (Kp s), x ≠ 0 ∧ qn x = 0) → QSA d β s) → HermitianPlaneStrongApprox σ β := by
  first | exact @GlobalTheory.CompanionTheory.PlaneSA.TwoQ.plane_strong_approx_of_quaternion | exact GlobalTheory.CompanionTheory.PlaneSA.TwoQ.plane_strong_approx_of_quaternion | (intros; apply GlobalTheory.CompanionTheory.PlaneSA.TwoQ.plane_strong_approx_of_quaternion <;> assumption)
