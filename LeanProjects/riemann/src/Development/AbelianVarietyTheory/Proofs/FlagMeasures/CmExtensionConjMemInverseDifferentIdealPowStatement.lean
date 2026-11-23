import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CmExtensionConjMemInverseDifferentIdealPow
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ImV
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN GlobalTheory.SnMass.SkewVol
open scoped TensorProduct ENNReal nonZeroDivisors Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cmExtension_conj_mem_inverseDifferentIdealPow : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (j : ℕ) (x : E), x ∈ dInv E j → σ x ∈ dInv E j := by
  first | exact @GlobalTheory.SnMass.VolN.conj_mem_dInv | exact GlobalTheory.SnMass.VolN.conj_mem_dInv | (intros; apply GlobalTheory.SnMass.VolN.conj_mem_dInv <;> assumption)
