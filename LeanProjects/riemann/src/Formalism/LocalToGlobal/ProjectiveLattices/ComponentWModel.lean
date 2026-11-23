import Formalism.LocalToGlobal.ProjectiveLattices.PetersonNormSubspace
import Formalism.LocalToGlobal.ProjectiveLattices.PartitionExtendByZeroAntitone

noncomputable section

namespace Formalism.L2.Pj

open NumberField Formalism.BasicNotions

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def LandherrSelfDual : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (D₁ D₂ : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H), D₁.p = D₂.p → D₁.q = D₂.q →
    ∃ (N : ℕ) (f : D₁.La →ₗ[𝓞 E] D₂.La), 0 < N ∧ Function.Injective f ∧
      ∀ x y, D₂.EF (f x) (f y) = (N : ℤ) ^ 2 * D₁.EF x y

variable {D : D7}

section Model

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD

end Model

end Formalism.L2.Pj

end
