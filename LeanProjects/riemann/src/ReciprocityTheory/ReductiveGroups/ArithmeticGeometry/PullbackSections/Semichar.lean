import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NonemptyUnitAt

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
  ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj

def PPSemicharSt : Prop :=
  ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), IsUnf U →
    ∀ (k : U.Comp) (x : (U.X k).dom) (W : UnfAt U k x) (Wu : UnitAt W),
      (∀ τ' i', ‖dmin (U.X k).Gm x.1 τ' i'‖ = 1) →
      ∀ a, Wu.χl (W.Pm a) = (-1 : ℂ) ^ ((W.F.Di (W.ik k)).EF a (H.w0 • a))

end ReciprocityTheory.ChartRestriction.G.PullbackSections
