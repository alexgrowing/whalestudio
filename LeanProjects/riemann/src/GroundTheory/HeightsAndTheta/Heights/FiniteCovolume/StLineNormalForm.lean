import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsComplementForm

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module

noncomputable section

section NormalForm

variable {F E : Type*} [Field F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W]

def LineNormalForm.Statement (h : HermitianForm F E W) : Prop :=
  ∀ D : ℕ, ∃ KK : Set (AddSubgroup E × AddSubgroup E), KK.Finite ∧ ∃ n : ℕ, 0 < n ∧
    ∀ (La : AddSubgroup W) (l : Submodule E W), IsDIntegral h D La → IsIsotropicLine h l →
      ∃ v w : W, v ∈ l ∧ IsHyperbolicPair h v w ∧
        (lineCoeffs (E := E) La v, lineCoeffs (E := E) La w) ∈ KK ∧
        ∀ x ∈ La, (n : E) * h.toSesq w x ∈ lineCoeffs (E := E) La v ∧
          (n : E) * h.toSesq v x ∈ lineCoeffs (E := E) La w

end NormalForm

section Inhabitants

open GaussianPlane

end Inhabitants

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
