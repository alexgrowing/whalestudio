import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsStabilizerLevi

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix Topology

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

def UnipRadicalOfRational.Statement (h : HermitianForm F E W) (v : Basis ι E W) : Prop :=
  ∀ (x₀ : W) (γ : h.unitaryGroup), γ • x₀ = x₀ →
    (∀ z : W, h.toSesq x₀ z = 0 → ∃ a : E, γ • z = z + a • x₀) →
    archEmbed h v γ ∈ unipRadical h v x₀

section Inhabitants

open GaussianPlane

end Inhabitants

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
