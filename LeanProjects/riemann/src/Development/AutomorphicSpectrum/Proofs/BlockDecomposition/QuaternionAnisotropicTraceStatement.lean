import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuaternionAnisotropicTrace
import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PlaneSupports.PlaneSupp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianPlaneStrongApprox
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published GlobalTheory.CompanionTheory.PlaneSA Topology
open scoped TensorProduct Quaternion
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quaternion_anisotropic_trace : ∀ {F K : Type} [Field F] [Field K] [Algebra F K] (d β : F), (2 : K) ≠ 0 →
  (∀ x : Q d β K, qn x = 0 → x = 0) → ∀ b : Q d β K, qn b = 1 → b.re ^ 2 ≠ 1 →
  ∀ r : K, r ^ 2 ≠ (2 * b.re) ^ 2 - 4 := by
  first | exact @GlobalTheory.CompanionTheory.PlaneSA.anis_trace_sq_sub_four_ne_sq | exact GlobalTheory.CompanionTheory.PlaneSA.anis_trace_sq_sub_four_ne_sq | (intros; apply GlobalTheory.CompanionTheory.PlaneSA.anis_trace_sq_sub_four_ne_sq <;> assumption)
