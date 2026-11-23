import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.LiftLaSpec

noncomputable section

namespace GlobalTheory.LevelGroupTest

open AlgebraicGeometry CategoryTheory Limits NumberField MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}

theorem natCast_mem_half (l : Level H) : (l.M : 𝓞 E) ∈ l.Mb := by
  have h : Ideal.span {(l.M : 𝓞 E)} ≤ l.Mb := by
    rw [← l.prod]; exact Ideal.mul_le_left
  exact h (Ideal.subset_span rfl)

attribute [local instance] Over.cartesianMonoidalCategory CategoryTheory.Hom.group

end GlobalTheory.LevelGroupTest
