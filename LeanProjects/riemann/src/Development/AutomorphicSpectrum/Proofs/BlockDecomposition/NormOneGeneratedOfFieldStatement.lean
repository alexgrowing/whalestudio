import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormOneGeneratedOfField
import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PlaneSupports.PlaneSupp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousSingleV
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published Sa2 GlobalTheory.CompanionTheory.SaGen
open scoped TensorProduct Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_one_generated_of_field : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (K : Type) [Field K] [Algebra F K], IsField (K ⊗[F] E) → NormOneGen (sigR K σ) := by
  first | exact @GlobalTheory.CompanionTheory.SaGen.NormOneField.normOne_of_isField | exact GlobalTheory.CompanionTheory.SaGen.NormOneField.normOne_of_isField | (intros; apply GlobalTheory.CompanionTheory.SaGen.NormOneField.normOne_of_isField <;> assumption)
