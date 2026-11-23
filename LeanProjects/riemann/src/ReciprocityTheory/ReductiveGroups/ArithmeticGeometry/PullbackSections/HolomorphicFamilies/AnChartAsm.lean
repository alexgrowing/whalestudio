import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.AnLawX
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ComposeLinearAction

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {σ' : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)} [Algebra c.F ℂ]

def anUvec (e' : Fin g ≃ Lt1 Dw) : Lt1 Dw → Fin g → ℂ := fun ℓ j => if j = e'.symm ℓ then 1 else 0

theorem anX_isChart [StarRing (𝓞 E)] (F : FamilyUnif Xo σ' ty) (i : Fin F.n) (P : (F.Di i).La →+ (Fin g → ℂ))
    (hP : IsPeriod (F.Di i) ty P) (y : FrPt Xo c ℂ) (hy : y.x = F.u i P) (e' : Fin g ≃ Lt1 Dw)
    (hder : ∀ ℓ : Lt1 Dw, IsDerivAt0 (anE F i P) (Pi.single (e'.symm ℓ) 1) (y.u ℓ.1 ℓ.2))
    (hPair : IsHolTo (Set.univ : Set (Fin (2 * g) → ℂ)) fun v =>
      pullback.lift (F.ex i P (anPr 0 v)).left (F.ex i P (anPr 1 v)).left
        ((Over.w (F.ex i P (anPr 0 v))).trans (Over.w (F.ex i P (anPr 1 v))).symm)) :
    IsChart y g (anFB ty).G.F (anFB ty).A.act (anUvec e') (anX F i P hP y hy) where
  zero m := anX_zero F i P hP y hy m
  trunc m := anX_trunc F i P hP y hy m
  law m := anX_law_chart F i P hP y hy hPair m
  act m a := anX_act F i P hP y hy m a
  tan ℓ := anX_tan F i P hP y hy (e'.symm ℓ) (y.u ℓ.1 ℓ.2) (hder ℓ)
  basis v := basis_single e' v

end ReciprocityTheory.ChartRestriction.G.PullbackSections
