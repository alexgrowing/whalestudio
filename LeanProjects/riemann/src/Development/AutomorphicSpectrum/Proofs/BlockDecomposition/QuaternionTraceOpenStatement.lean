import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuaternionTraceOpen
import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PlaneSupports.PlaneSupp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianPlaneStrongApprox
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published GlobalTheory.CompanionTheory.PlaneSA Topology
open scoped TensorProduct Quaternion
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quaternion_trace_open : ∀ {F K : Type} [Field F] [Field K] [Algebra F K] [TopologicalSpace K] [IsTopologicalDivisionRing K] (d β : F)
  (a : Q d β K), qn a = 1 → a.re ^ 2 ≠ 1 →
  (∀ V ∈ 𝓝 (1 : K), ∀ᶠ x in 𝓝 (1 : K), ∃ μ ∈ V, μ ^ 2 = x) →
  ∀ U ∈ 𝓝 a, ∀ᶠ r in 𝓝 a.re, ∃ b ∈ U, qn b = 1 ∧ b.re = r := by
  first | exact @GlobalTheory.CompanionTheory.PlaneSA.re_normOne_open_of_sq_ne_one | exact GlobalTheory.CompanionTheory.PlaneSA.re_normOne_open_of_sq_ne_one | (intros; apply GlobalTheory.CompanionTheory.PlaneSA.re_normOne_open_of_sq_ne_one <;> assumption)
