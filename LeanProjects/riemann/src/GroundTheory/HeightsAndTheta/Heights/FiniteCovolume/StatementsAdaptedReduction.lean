import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsComplementForm

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module
open scoped Pointwise

noncomputable section

section Reduction

variable {F E : Type*} [Field F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W]

def AdaptedReduction.Statement [FiniteDimensional E W] (h : HermitianForm F E W) : Prop :=
  ∀ v₀ w₀ : W, IsHyperbolicPair h v₀ w₀ → ∀ h' : HermitianForm F E (hypComplement h v₀ w₀),
    (∀ x y, h'.toSesq x y = h.toSesq x y) → ∀ D : ℕ,
    ∃ KK : Set (AddSubgroup E × AddSubgroup E), KK.Finite ∧ ∃ n D' : ℕ, 0 < n ∧
      ∀ (La : AddSubgroup W) (l : Submodule E W), IsDIntegral h D La → IsIsotropicLine h l →
        ∃ (g : h.unitaryGroup) (La₁ : AddSubgroup W), g • La₁ = La ∧ g • v₀ ∈ l ∧
          (lineCoeffs (E := E) La₁ v₀, lineCoeffs (E := E) La₁ w₀) ∈ KK ∧
          (∀ x ∈ La₁, ∃ a ∈ lineCoeffs (E := E) La₁ v₀, ∃ b ∈ lineCoeffs (E := E) La₁ w₀,
            n • x - a • v₀ - b • w₀ ∈ hypComplement h v₀ w₀) ∧
          IsDIntegral h' D' (La₁.comap (hypComplement h v₀ w₀).subtype.toAddMonoidHom)

end Reduction

section Inhabitants

open GaussianPlane

end Inhabitants

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
