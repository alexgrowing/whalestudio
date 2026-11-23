import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuaternionIntegralTraceAlmostAll
import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PlaneSupports.PlaneSupp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianPlaneStrongApprox
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published GlobalTheory.CompanionTheory.PlaneSA Topology
open scoped TensorProduct Quaternion
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quaternion_integral_trace_almost_all : ∀ {F : Type} [Field F] [NumberField F] (d β : F), d ≠ 0 → β ≠ 0 →
  ∀ᶠ v in Filter.cofinite (α := HeightOneSpectrum (𝓞 F)), ∀ t ∈ Ov v,
    ∃ b : Q d β (Kp (Sum.inr v : Pl F)), qn b = 1 ∧ 2 * b.re = t ∧ IntQ v b := by
  first | exact @GlobalTheory.CompanionTheory.PlaneSA.exists_integral_norm_one_trace | exact GlobalTheory.CompanionTheory.PlaneSA.exists_integral_norm_one_trace | (intros; apply GlobalTheory.CompanionTheory.PlaneSA.exists_integral_norm_one_trace <;> assumption)
