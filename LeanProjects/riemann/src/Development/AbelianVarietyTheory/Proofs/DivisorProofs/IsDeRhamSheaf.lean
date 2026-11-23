import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PoincareDeRhamDuality
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ZeroSectionBase

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
  GlobalTheory.DeRham

namespace GlobalTheory.DeRhamSheaf

variable {T : Scheme.{0}} (A : Over T) [GrpObj A]

abbrev onAff {V : T.Opens} (hV : IsAffineOpen V) : Over (Sp Γ(T, V)) :=
  (Over.pullback hV.fromSpec).obj A

instance {V : T.Opens} (hV : IsAffineOpen V) : GrpObj (onAff A hV) := Functor.grpObjObj

abbrev resAlg {V V' : T.Opens} (h : V' ≤ V) : Algebra Γ(T, V) Γ(T, V') :=
  (T.presheaf.map (homOfLE h).op).hom.toAlgebra

def IsDeRhamSheaf (H : T.Modules) : Prop :=
  ∃ e : ∀ (V : T.Opens) (hV : IsAffineOpen V), Γ(H, V) ≃ₗ[Γ(T, V)] primDR (onAff A hV),
    ∀ (V V' : T.Opens) (hV : IsAffineOpen V) (hV' : IsAffineOpen V') (h : V' ≤ V),
      letI := resAlg h
      ∀ (φ : (onAff A hV').left ⟶ (onAff A hV).left)
        (hφ : IsGrpPullback (onAff A hV') (onAff A hV) (spMap (algebraMap Γ(T, V) Γ(T, V'))) φ),
        φ ≫ pullback.fst A.hom hV.fromSpec = pullback.fst A.hom hV'.fromSpec →
        ∀ s : Γ(H, V), e V' hV' (GlobalTheory.Twist.resM H h s) = (GlobalTheory.Published.AbelianDeRham.bcMor hφ).pull (e V hV s)

end GlobalTheory.DeRhamSheaf
