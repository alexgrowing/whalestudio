import Formalism.LocalToGlobal.ProjectiveLattices.EquivariantFiniteGroup
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FlowCoefficientBounds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CuspCoefficientFlow
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.EmbeddingHermitianPairs

noncomputable section

namespace Formalism.L2.Pj.CompSplitPfA

open NumberField Complex MeasureTheory ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

structure IsIdemFn (X : Data E r) (χ : Frame X.Ψ r → ℂ) : Prop where
  zo : ∀ x ∈ X.dom, χ x = 0 ∨ χ x = 1
  hol : DifferentiableOn ℂ χ X.dom
  bor : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, χ (rmul x b) = χ x
  gam : ∀ γ ∈ X.Γ, ∀ x ∈ X.dom, χ (lact γ x) = χ x

def compSplitPfA_mulL {ι : Type} (X : ι → Data E r) (χ : Formalism.L2.Pj.FDSec X) :
    Formalism.L2.Pj.FDSec X →ₗ[ℂ] Formalism.L2.Pj.FDSec X where
  toFun P := fun k => χ k * P k
  map_add' P Q := by
    funext k x
    simp [mul_add]
  map_smul' a P := by
    funext k x
    simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

end Formalism.L2.Pj.CompSplitPfA
