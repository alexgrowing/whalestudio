import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIntegerAddConjEqOneOfFormallyUnramified
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ImV
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN GlobalTheory.SnMass.SkewVol
open scoped TensorProduct ENNReal nonZeroDivisors Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integer_add_conj_eq_one_of_formallyUnramified' : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → Algebra.FormallyUnramified (𝓞 F) (𝓞 E) → ∃ θ : 𝓞 E, (θ : E) + σ θ = 1 := by
  first | exact @GlobalTheory.exists_integer_add_conj_eq_one_of_formallyUnramified | exact GlobalTheory.exists_integer_add_conj_eq_one_of_formallyUnramified | (intros; apply GlobalTheory.exists_integer_add_conj_eq_one_of_formallyUnramified <;> assumption)
