import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatPath

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

namespace GlobalTheory.Nef

theorem stalk_formallySmooth_of_smooth : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], Smooth G.hom → ∀ (s : S) (π : S.presheaf.stalk s →+* G.left.presheaf.stalk (unitSec G s)) (ε : G.left.presheaf.stalk (unitSec G s) →+* S.presheaf.stalk s) (m : G.left.presheaf.stalk (unitSec G s) →+* G.left.presheaf.stalk (unitSec G s)), StalkData G s π ε m → π.FormallySmooth := by
  intro S G _ hG s π ε m h
  have hstr := h.str
  clear h
  revert π hstr
  have hs : G.hom.base (unitSec G s) = s := by
    rw [← Scheme.Hom.comp_apply, unitSec, sec_hom]
    rfl
  generalize unitSec G s = p at hs ⊢
  subst hs
  intro π hstr
  have e : Spec.map (CommRingCat.ofHom π) = Spec.map (G.hom.stalkMap p) :=
    (cancel_mono (S.fromSpecStalk (G.hom.base p))).1 (by
      rw [hstr, Scheme.SpecMap_stalkMap_fromSpecStalk])
  have e' : π = (G.hom.stalkMap p).hom := congrArg CommRingCat.Hom.hom (Spec.map_injective e)
  rw [e']
  exact Scheme.Hom.mem_smoothLocus.mp (G.hom.smoothLocus_eq_top.ge (Set.mem_univ p))

end GlobalTheory.Nef
