import Mathlib
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

set_option backward.isDefEq.respectTransparency false in

theorem isClosedImmersion_pullback_map_of_genericPoint {W U : Scheme.{0}} [IsIntegral W] {j : U ⟶ W}
    (hj : GlobalTheory.IsGenericPointHom j) {A B : Over W} (u : A ⟶ B) {A' B' : Over U} {a : A'.left ⟶ A.left}
    {b : B'.left ⟶ B.left} (v : A' ⟶ B') (ha : IsPullback a A'.hom A.hom j) (hb : IsPullback b B'.hom B.hom j)
    (hv : v.left ≫ b = a ≫ u.left) (hc : IsClosedImmersion v.left) (k : Type) [Field k] (g : Sp k ⟶ W)
    (hg : g (IsLocalRing.closedPoint k) = genericPoint W) :
    IsClosedImmersion ((Over.pullback g).map u).left := by
  obtain ⟨l, hl⟩ := GlobalTheory.StalkLimit.exists_lift_fromSpecStalk (genericPoint W) g (fun V hV y _ => by
    have hy : y = IsLocalRing.closedPoint k := Subsingleton.elim (α := PrimeSpectrum k) _ _
    subst hy
    change g (IsLocalRing.closedPoint k) ∈ V
    rwa [hg])
  obtain ⟨e, he⟩ := hj
  have hg' : (l ≫ e.inv) ≫ j = g := by
    rw [← he, Category.assoc, e.inv_hom_id_assoc, hl]
  have S2 : IsPullback a v.left u.left b := by
    refine IsPullback.of_bot ?_ hv.symm hb
    rw [Over.w, Over.w]
    exact ha
  have h1 : ((Over.pullback g).map u).left ≫ pullback.fst B.hom g = pullback.fst A.hom g ≫ u.left := by
    simp
  have h2 : ((Over.pullback g).map u).left ≫ pullback.snd B.hom g = pullback.snd A.hom g := by
    simp
  have S1 : IsPullback (pullback.fst A.hom g) ((Over.pullback g).map u).left u.left (pullback.fst B.hom g) := by
    refine IsPullback.of_bot ?_ h1.symm (IsPullback.of_hasPullback B.hom g)
    rw [h2, Over.w]
    exact IsPullback.of_hasPullback A.hom g
  let m : pullback B.hom g ⟶ B'.left := hb.lift (pullback.fst B.hom g) (pullback.snd B.hom g ≫ l ≫ e.inv) (by
    rw [Category.assoc, hg', pullback.condition])
  have hm : m ≫ b = pullback.fst B.hom g := hb.lift_fst _ _ _
  let n : pullback A.hom g ⟶ A'.left := S2.lift (pullback.fst A.hom g) (((Over.pullback g).map u).left ≫ m) (by
    rw [Category.assoc, hm, h1])
  have hn : n ≫ a = pullback.fst A.hom g := S2.lift_fst _ _ _
  have hn' : n ≫ v.left = ((Over.pullback g).map u).left ≫ m := S2.lift_snd _ _ _
  have S3 : IsPullback n ((Over.pullback g).map u).left v.left m := by
    refine IsPullback.of_right ?_ hn' S2
    rw [hn, hm]
    exact S1
  exact MorphismProperty.of_isPullback (P := @IsClosedImmersion) S3 hc

end GlobalTheory
