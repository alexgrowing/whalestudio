import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeStabilizerVolumeAlmostAll
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCovolOne
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_stabilizer_volume_almost_all : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (n d : ℕ) (b : Module.Basis (Fin d) F E), ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ lam : Measure (Fv F v), IsStdV v lam → ∀ (m : Measure (Fin n → Fin M → Fv F v ⊗[F] E)) (g : HA (Fv F v) σ (hypOne J)), latStab σ (hypOne J) b v g → stageInt (Fv F v) σ J b lam m ((latV b v).indicator 1) g = m (latV b v) := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Stab.stageInt_latStab | exact GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Stab.stageInt_latStab | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Stab.stageInt_latStab <;> assumption)
