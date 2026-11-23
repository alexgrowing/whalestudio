import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfGroupPullbackDataBase
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

set_option autoImplicit false

namespace GlobalTheory.EndLoc.HomGlue

theorem Pt.comp_f_eq {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B] {L : LB A.left} {M : LB B.left}
    {Z W : Scheme.{0}} {x x' : Pt A B L M Z} (e : x = x') (p : W ⟶ pullback A.hom x.t)
    (q : W ⟶ pullback A.hom x'.t) (h1 : p ≫ pullback.fst _ _ = q ≫ pullback.fst _ _)
    (h2 : p ≫ pullback.snd _ _ = q ≫ pullback.snd _ _) : p ≫ x.f = q ≫ x'.f := by
  subst e
  obtain rfl : p = q := pullback.hom_ext h1 h2
  rfl

theorem Pt.ext_cover : ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] [GrpObj B] (L : LB A.left) (M : LB B.left)
    (hL : L.IsLB) (hM : M.IsLB) (Z : Scheme.{0}) (𝒰 : Z.OpenCover) (y y' : HomGlue.Pt A B L M Z),
    (∀ i, y.map hL hM (𝒰.f i) = y'.map hL hM (𝒰.f i)) → y = y' := by
  intro S A B _ _ L M hL hM Z 𝒰 y y' h
  have ht : y.t = y'.t := 𝒰.hom_ext _ _ fun i => congrArg Pt.t (h i)
  obtain ⟨t, f, w⟩ := y
  obtain ⟨t', f', w'⟩ := y'
  dsimp only at ht
  subst ht
  suffices hf : f = f' by subst hf; rfl
  refine (Scheme.Pullback.openCoverOfRight 𝒰 A.hom t).hom_ext _ _ fun (i : 𝒰.I₀) => ?_
  have := Pt.comp_f_eq (h i) (𝟙 _) (𝟙 _) rfl rfl
  change 𝟙 _ ≫ pmap A t (𝒰.f i) ≫ f = 𝟙 _ ≫ pmap A t (𝒰.f i) ≫ f' at this
  rw [Category.id_comp, Category.id_comp] at this
  have e : (Scheme.Pullback.openCoverOfRight 𝒰 A.hom t).f i = pmap A t (𝒰.f i) := by
    rw [Scheme.Pullback.openCoverOfRight_f]
    apply pullback.hom_ext
    · erw [pullback.lift_fst]
    · erw [pullback.lift_snd]
  rw [e]
  exact this

end GlobalTheory.EndLoc.HomGlue
