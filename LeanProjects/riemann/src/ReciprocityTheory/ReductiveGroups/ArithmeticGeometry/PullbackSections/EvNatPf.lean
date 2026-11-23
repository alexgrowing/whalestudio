import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.IndepPts
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  (Xo : Moduli Dw l) (c : Coeff l)

def EvNat : Prop :=
  ∀ f : Rul Xo c, IsNatural (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) f →
    ∀ (S T : Type) [CommRing S] [IsReduced S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T)
      (y : FrPt Xo c S) (z : FrPt Xo c T), FrMap φ y z → evR Xo c f z = φ (evR Xo c f y)

theorem evNat_of (hWD : EvalWD (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z))
    (hA : AllTest Xo c) : EvNat Xo c := by
  intro f hf S T _ _ _ _ _ φ y z hz
  obtain ⟨p, ψ, y', hy'⟩ := hA S y
  have h1 : evR Xo c f y = ψ (f p y') :=
    evalAt_eq_of (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) hWD f hf p ψ y' y hy'
  have h2 : evR Xo c f z = (φ.comp ψ) (f p y') :=
    evalAt_eq_of (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) hWD f hf p (φ.comp ψ) y' z
      (frMap_trans (Xo := Xo) (c := c) _ _ _ ψ φ y' y z hy' hz)
  rw [h2, h1, AlgHom.comp_apply]

end ReciprocityTheory.ChartRestriction.G.PullbackSections
