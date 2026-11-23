import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExpandsPullOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdFam
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TWMain
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadraticAlgebraValuation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.PowKernel

theorem pow_ext {S : Scheme.{0}} {G' G : Over S} [GrpObj G'] [GrpObj G] {j : ℕ} (p : IsPowGrp G' G j)
    {X : Over S} {x y : X ⟶ G'} (h : ∀ l, x ≫ p.pr l = y ≫ p.pr l) : x = y :=
  Fan.IsLimit.hom_ext p.lim x y h

theorem one_pr {S : Scheme.{0}} {G' G : Over S} [GrpObj G'] [GrpObj G] {j : ℕ} (p : IsPowGrp G' G j)
    (l : Fin j) : η[G'] ≫ p.pr l = η[G] := by
  haveI := p.hom l
  exact IsMonHom.one_hom (p.pr l)

theorem main : ∀ (S : Scheme.{0}) (T' T G' G B' B : Over S) [GrpObj T'] [GrpObj T] [GrpObj G'] [GrpObj G] [GrpObj B'] [GrpObj B] (j : ℕ) (pT : IsPowGrp T' T j) (p : IsPowGrp G' G j) (pB : IsPowGrp B' B j) (i : T ⟶ G) (q : G ⟶ B) (i' : T' ⟶ G') (q' : G' ⟶ B'), (∀ l, i' ≫ p.pr l = pT.pr l ≫ i) → (∀ l, q' ≫ pB.pr l = p.pr l ≫ q) → IsPullback i (toUnit T) q η[B] → IsPullback i' (toUnit T') q' η[B'] := by
  intro S T' T G' G B' B _ _ _ _ _ _ j pT p pB i q i' q' hi hq h

  have w : i' ≫ q' = toUnit T' ≫ η[B'] := by
    apply pow_ext pB
    intro l
    rw [Category.assoc, Category.assoc, hq l, one_pr pB l, ← Category.assoc, hi l,
      Category.assoc, h.w, ← Category.assoc, toUnit_unique (pT.pr l ≫ toUnit T) (toUnit T')]

  have key : ∀ (s : PullbackCone q' η[B']) (l : Fin j),
      (s.fst ≫ p.pr l) ≫ q = s.snd ≫ η[B] := by
    intro s l
    rw [Category.assoc, ← hq l, ← Category.assoc, s.condition, Category.assoc, one_pr pB l]
  have fac : ∀ (s : PullbackCone q' η[B']) (l : Fin j),
      Fan.IsLimit.lift pT.lim (fun l => h.lift (s.fst ≫ p.pr l) s.snd (key s l)) ≫ pT.pr l =
        h.lift (s.fst ≫ p.pr l) s.snd (key s l) :=
    fun s l => Fan.IsLimit.fac pT.lim _ l
  refine IsPullback.of_isLimit (c := PullbackCone.mk i' (toUnit T') w)
    (PullbackCone.IsLimit.mk w
      (fun s => Fan.IsLimit.lift pT.lim (fun l => h.lift (s.fst ≫ p.pr l) s.snd (key s l)))
      ?_ ?_ ?_)
  · intro s
    apply pow_ext p
    intro l
    rw [Category.assoc, hi l, ← Category.assoc, fac s l, h.lift_fst]
  · intro s
    exact toUnit_unique _ _
  · intro s m hm _
    apply pow_ext pT
    intro l
    rw [fac s l]
    apply h.hom_ext
    · rw [h.lift_fst, Category.assoc, ← hi l, ← Category.assoc, hm]
    · rw [h.lift_snd]
      exact toUnit_unique _ _

end GlobalTheory.PowKernel
