import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NonemptyUnitAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.TorusAtData

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
  ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

def TorusPins {U : Unf Xo c σ r} {k : U.Comp} {x : (U.X k).dom} (W : UnfAt U k x) (Wu : UnitAt W)
    (A : ReciprocityTheory.ChartRestriction.G.I2.TorusAt (U.X k) x.1) (L : (Fin W.g → ℂ) →ₗ[ℂ] ReciprocityTheory.ChartRestriction.G.I2.Vsp A.T.dim) : Prop :=
  (∀ a, A.φ ((W.φ k a : (U.X k).Λ) : Fin r → E) = L (star (W.Pm a))) ∧
  (∀ z z', ReciprocityTheory.ChartRestriction.G.I2.Hf (L z) (L z') = star (hermForm Wu.Hm (star z) (star z'))) ∧
  (∀ z, A.s (fun _ => L z) = star (Wu.θ (star z))) ∧
  (∀ a, ((A.T.eps (A.φ ((W.φ k a : (U.X k).Λ) : Fin r → E)) : ℤ) : ℂ) = Wu.χl (W.Pm a))

end ReciprocityTheory.ChartRestriction.G.PullbackSections
