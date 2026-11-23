import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CmExtensionImaginaryGenerator
import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PlaneSupports.PlaneSupp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianPlaneStrongApprox
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published GlobalTheory.CompanionTheory.PlaneSA Topology
open scoped TensorProduct Quaternion
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_extension_imaginary_generator : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
  IsCMExt F E σ → ∃ d : F, (∀ r : F, r ^ 2 ≠ d) ∧ ∃ ξ : E, ξ ^ 2 = algebraMap F E d ∧ σ ξ = -ξ := by
  first | exact @GlobalTheory.CompanionTheory.PlaneSA.cm_exists_sqrt_nonsquare | exact GlobalTheory.CompanionTheory.PlaneSA.cm_exists_sqrt_nonsquare | (intros; apply GlobalTheory.CompanionTheory.PlaneSA.cm_exists_sqrt_nonsquare <;> assumption)
