import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalContentZetaSeries
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsContent
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep GlobalTheory.CompanionTheory.WeilSiegel.HypMass
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_content_zeta_series : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∃ (ι : Type) (_ : Countable ι) (c : ι → Fv F v ⊗[F] E) (w : ι → ℕ), IsContent σ b v c w ∧ ∀ s : ℕ, 1 ≤ s → HasSum (fun i => (((qv v : ℝ) ^ w i)⁻¹) ^ s) (zetaV E v s) := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.HypMass.Content.content | exact GlobalTheory.CompanionTheory.WeilSiegel.HypMass.Content.content | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.HypMass.Content.content <;> assumption)
