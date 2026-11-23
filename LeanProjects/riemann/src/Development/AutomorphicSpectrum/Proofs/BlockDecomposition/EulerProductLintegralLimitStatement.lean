import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EulerProductLintegralLimit
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCovolOne
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.euler_product_lintegral_limit : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (S : Finset (HeightOneSpectrum (𝓞 F))) (Ψinf : (Fin 1 → Fin (M + 2) → Ainf F ⊗[F] E) → ℝ≥0∞) (Ψ : ∀ v : HeightOneSpectrum (𝓞 F), (Fin 1 → Fin (M + 2) → Fv F v ⊗[F] E) → ℝ≥0∞), Measurable Ψinf → (∀ v, Measurable (Ψ v)) → Measurable (purePr σ J b S Ψinf Ψ) := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.HypStep.PrimMeas.measurable_purePr | exact GlobalTheory.CompanionTheory.WeilSiegel.HypStep.PrimMeas.measurable_purePr | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.HypStep.PrimMeas.measurable_purePr <;> assumption)
