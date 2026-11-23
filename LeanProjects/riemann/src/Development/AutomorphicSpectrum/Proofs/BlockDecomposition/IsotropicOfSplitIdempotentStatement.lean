import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsotropicOfSplitIdempotent
import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PlaneSupports.PlaneSupp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousSingleV
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published Sa2 GlobalTheory.CompanionTheory.SaGen
open scoped TensorProduct Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isotropic_of_split_idempotent : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ {M : ℕ} (J : Matrix (Fin M) (Fin M) E), 2 ≤ M → IsHermND σ J → ∀ (K : Type) [Field K] [Algebra F K] (e : K ⊗[F] E), e * e = e → e + sigR K σ e = 1 → e * sigR K σ e = 0 → IsoAt K σ J := by
  first | exact @GlobalTheory.CompanionTheory.SaGen.IsoSplit.isoAt_of_split | exact GlobalTheory.CompanionTheory.SaGen.IsoSplit.isoAt_of_split | (intros; apply GlobalTheory.CompanionTheory.SaGen.IsoSplit.isoAt_of_split <;> assumption)
