import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AdelicCharacterOrthogonalIsRational
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsCovolOne
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV
open scoped TensorProduct ENNReal Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelic_character_orthogonal_is_rational : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ → ∀ x : AF F, (∀ t : F, ψ (algebraMap F (AF F) t * x) = 1) → ∃ c : F, x = algebraMap F (AF F) c := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Ann.annihilator_eq | exact GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Ann.annihilator_eq | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Ann.annihilator_eq <;> assumption)
