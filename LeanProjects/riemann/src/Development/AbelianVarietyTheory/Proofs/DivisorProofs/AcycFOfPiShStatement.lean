import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AcycFOfPiSh
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.acycF_of_pi_sh' : ∀ (R : Type) [CommRing R] (F : Shv R) (ι : Type) [Finite ι] (T : ι → Type) [∀ i, CommRing (T i)] (B : Type) [CommRing B], Nonempty (B ≃+* (∀ i, T i)) → (∀ i, SH (T i)) → AcycF R (sp B) F := by
  first | exact @GlobalTheory.EtC.acycF_of_pi_sh | exact GlobalTheory.EtC.acycF_of_pi_sh | (intros; apply GlobalTheory.EtC.acycF_of_pi_sh <;> assumption)
