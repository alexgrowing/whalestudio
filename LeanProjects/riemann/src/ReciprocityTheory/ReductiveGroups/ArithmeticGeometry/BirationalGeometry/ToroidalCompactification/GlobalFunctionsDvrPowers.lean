import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.GlobFnsDvr
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

open scoped CategoryTheory.Obj

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor.GlobalFunctionsDvrPowers

open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out

def pullPowIso {S S' : Scheme.{0}} (f : S' ⟶ S) (G : Over S) :
    ∀ n : ℕ, (Over.pullback f).obj (powObj G n) ≅ powObj ((Over.pullback f).obj G) n
  | 0 => (Functor.Monoidal.εIso (Over.pullback f)).symm
  | n + 1 => (Functor.Monoidal.μIso (Over.pullback f) G (powObj G n)).symm ≪≫
      whiskerLeftIso ((Over.pullback f).obj G) (pullPowIso f G n)

theorem bijective_of_iso {S' : Scheme.{0}} {A B : Over S'} (e : A ≅ B)
    (h : Function.Bijective B.hom.appTop.hom) : Function.Bijective A.hom.appTop.hom := by
  have hw : A.hom = e.hom.left ≫ B.hom := (Over.w e.hom).symm
  rw [hw, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.coe_comp]
  refine Function.Bijective.comp ?_ h
  refine Function.bijective_iff_has_inverse.2 ⟨(e.inv.left.appTop).hom, fun x => ?_, fun x => ?_⟩
  · show (e.hom.left.appTop ≫ e.inv.left.appTop).hom x = x
    rw [← Scheme.Hom.comp_appTop, ← Over.comp_left, e.inv_hom_id]
    simp
  · show (e.inv.left.appTop ≫ e.hom.left.appTop).hom x = x
    rw [← Scheme.Hom.comp_appTop, ← Over.comp_left, e.hom_inv_id]
    simp

theorem pull_powObj_globalFns (hGF : ReciprocityTheory.ChartRestriction.G.Out.GlobalFnsSt) {S S' : Scheme.{0}} (f : S' ⟶ S)
    (G : Over S) [GrpObj G] (hG : ReciprocityTheory.ChartRestriction.G.Semi.IsSemiAbelian G)
    [IsProper ((Over.pullback f).obj G).hom] (n : ℕ) :
    Function.Bijective ((Over.pullback f).obj (powObj G n)).hom.appTop.hom := by
  exact bijective_of_iso (pullPowIso f G n)
    (ReciprocityTheory.ChartRestriction.G.Geo.Tor.AbelianSchemeGerms.globalFns_powObj hGF ((Over.pullback f).obj G)
      (ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsSemiAbelian.pullback (f := f) (G := G) hG) n)

end ReciprocityTheory.ChartRestriction.G.Geo.Tor.GlobalFunctionsDvrPowers
