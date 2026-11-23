import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.WtFieldPfA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeA

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

theorem tanAdd_holds (Xo : Moduli Dw l) : TanAddSt Xo := by
  intro S _ x w hw a b u₁ u₂ h₁ h₂
  have e₁ : u₁ = smT x a (ovT (t := Xo.univ.t) hw) := Over.OverMorphism.ext h₁
  have e₂ : u₂ = smT x b (ovT (t := Xo.univ.t) hw) := Over.OverMorphism.ext h₂
  rw [e₁, e₂, ← smT_add x _ (smT_zero_ovT hw)]
  rfl

end ReciprocityTheory.ChartRestriction.G.PullbackSections
