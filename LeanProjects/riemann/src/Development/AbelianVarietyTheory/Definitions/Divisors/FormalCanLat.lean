import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CanExtOfCharts

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.LogKS GlobalTheory.LogDR GlobalTheory.CanExtM
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CanExtM

def FormalCanLat : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H) (k : Type) [Field k] [CharZero k]
    (m d : ℕ) (t : SAB H (Sp (ChartRing k m d))) (P : PELUnif (IsLocalRing.maximalIdeal (ChartRing k m d)) t)
    (gam : Fin m → levelForms H l.M' P.D.toPre.X),
    IsMonomial P.D.toPre (bdParam k m d) (fun i => gam i) → IsPartOfBasis gam →
    ∃ (c : GlobalTheory.LogDR.Chart t (show (Sp (ChartRing k m d)).Opens from PrimeSpectrum.basicOpen (∏ i, bdParam k m d i)))
      (L : Submodule Γ(Sp (ChartRing k m d), c.U.1) (HdR c.A)),
      c.U.1 = ⊤ ∧ IsCanLattice (spMap (Int.castRingHom (ChartRing k m d))) c L

end GlobalTheory.CanExtM
