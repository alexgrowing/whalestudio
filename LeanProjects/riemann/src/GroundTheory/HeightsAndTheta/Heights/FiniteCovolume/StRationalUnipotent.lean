import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsStabilizerLevi

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix Topology

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W]

def RationalUnipotent.Statement (h : HermitianForm F E W) : Prop :=
  ∀ (D : ℕ) (La : AddSubgroup W) (x₀ w₀ : W), IsDIntegral h D La → x₀ ∈ La →
    IsHyperbolicPair h x₀ w₀ →
    ∃ m : ℕ, 0 < m ∧ ∀ (y : W) (c : E), y ∈ hypComplement h x₀ w₀ → (∃ z ∈ La, y = m • z) →
      (∃ a : 𝓞 E, c = (m : E) * a) → c + conj F E c = -h.toSesq y y →
      ∃ γ ∈ latticeStab h La, γ • x₀ = x₀ ∧ γ • w₀ = w₀ + y + c • x₀ ∧
        ∀ z ∈ hypComplement h x₀ w₀, γ • z = z - h.toSesq y z • x₀

section Inhabitants

open GaussianPlane

end Inhabitants

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
