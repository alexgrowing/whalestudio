import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.Slopes

namespace GlobalTheory.CompanionTheory.Ar.Lines

open NumberField TensorProduct GroundTheory.Heights₂.Heights

noncomputable section

def gramMat {L : Type} [Field L] [NumberField L] (B : HermitianBundle.{0} L) (σ : L →+* ℂ) {i : ℕ}
    (f : Fin i → B.carrier) : Matrix (Fin i) (Fin i) ℂ :=
  Matrix.of fun a b => (B.metric.form σ).inner ((1 : ComplexAt σ) ⊗ₜ[𝓞 L] f a) ((1 : ComplexAt σ) ⊗ₜ[𝓞 L] f b)

end

end GlobalTheory.CompanionTheory.Ar.Lines
