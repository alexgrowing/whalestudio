import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TensorInvolutionInvolutive
import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PlaneSupports.PlaneSupp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousSingleV
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published Sa2 GlobalTheory.CompanionTheory.SaGen
open scoped TensorProduct Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensor_involution_involutive : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (K : Type) [Field K] [Algebra F K] (t : K ⊗[F] E), sigR K σ (sigR K σ t) = t := by
  first | exact @GlobalTheory.CompanionTheory.SaGen.sigR_sigR_eq | exact GlobalTheory.CompanionTheory.SaGen.sigR_sigR_eq | (intros; apply GlobalTheory.CompanionTheory.SaGen.sigR_sigR_eq <;> assumption)
