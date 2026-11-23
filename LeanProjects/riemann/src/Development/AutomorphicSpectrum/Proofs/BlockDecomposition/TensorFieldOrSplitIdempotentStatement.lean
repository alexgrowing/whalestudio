import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TensorFieldOrSplitIdempotent
import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PlaneSupports.PlaneSupp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousSingleV
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published Sa2 GlobalTheory.CompanionTheory.SaGen
open scoped TensorProduct Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensor_field_or_split_idempotent : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (K : Type) [Field K] [Algebra F K], IsField (K ⊗[F] E) ∨ ∃ e : K ⊗[F] E, e * e = e ∧ e + sigR K σ e = 1 ∧ e * sigR K σ e = 0 := by
  first | exact @GlobalTheory.CompanionTheory.SaGen.Dichotomy.field_or_split | exact GlobalTheory.CompanionTheory.SaGen.Dichotomy.field_or_split | (intros; apply GlobalTheory.CompanionTheory.SaGen.Dichotomy.field_or_split <;> assumption)
