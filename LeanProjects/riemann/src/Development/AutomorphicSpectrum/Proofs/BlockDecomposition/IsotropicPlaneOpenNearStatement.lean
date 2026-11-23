import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsotropicPlaneOpenNear
import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PlaneSupports.PlaneSupp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousSingleV
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published Sa2 GlobalTheory.CompanionTheory.SaGen
open scoped TensorProduct Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isotropic_plane_open_near : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ {M : ℕ} (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ {K : Type} [NontriviallyNormedField K] [ProperSpace K] [Algebra F K], IsoAt K σ J → ∃ a₀ b₀ : Fin M → K ⊗[F] E, ∀ᶠ p in nhds (a₀, b₀), IsoPlane K σ J p.1 p.2 := by
  first | exact @GlobalTheory.CompanionTheory.SaGen.IsoOpen.isoPlane_eventually | exact GlobalTheory.CompanionTheory.SaGen.IsoOpen.isoPlane_eventually | (intros; apply GlobalTheory.CompanionTheory.SaGen.IsoOpen.isoPlane_eventually <;> assumption)
