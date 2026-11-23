import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AnisotropicUnitaryGroupCompact
import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PlaneSupports.PlaneSupp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousSingleV
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published Sa2 GlobalTheory.CompanionTheory.SaGen
open scoped TensorProduct Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.anisotropic_unitary_group_compact : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ {M : ℕ} (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ {K : Type} [NontriviallyNormedField K] [ProperSpace K] [Algebra F K], IsField (K ⊗[F] E) → ¬ IsoAt K σ J → IsCompact (Set.univ : Set (HA K σ J)) := by
  first | exact @GlobalTheory.CompanionTheory.SaGen.CompactField.isCompact_univ_HA | exact GlobalTheory.CompanionTheory.SaGen.CompactField.isCompact_univ_HA | (intros; apply GlobalTheory.CompanionTheory.SaGen.CompactField.isCompact_univ_HA <;> assumption)
