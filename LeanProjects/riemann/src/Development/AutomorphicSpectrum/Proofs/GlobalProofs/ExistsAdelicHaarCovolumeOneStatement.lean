import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsAdelicHaarCovolumeOne
import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsCovolOne
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV
open scoped TensorProduct ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_adelic_haar_covolume_one : ∀ (F : Type) [Field F] [NumberField F], ∃ db : Measure (AF F), IsCovolOne db := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.OneV.exists_isCovolOne | exact GlobalTheory.CompanionTheory.Hypotheses₂.OneV.exists_isCovolOne | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.OneV.exists_isCovolOne <;> assumption)
