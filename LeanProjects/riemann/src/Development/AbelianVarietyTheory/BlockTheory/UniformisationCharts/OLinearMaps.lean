import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.RosatiAdj
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegUnif

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.IndefiniteRowSideFullHecke.OLinearMaps

open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R}

structure GtCommutes {D : DegPre R} {e : ℕ} {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
    [IsCommMonObj G] (g : GtCoord I D e G) (f : G ⟶ G) (b b' : D.P.A ⟶ D.P.A)
    (σ : D.X → D.X) : Prop where
  q_comm : (Over.pullback (thick R I e)).map f ≫ g.q =
    g.q ≫ (Over.pullback (thick R I e)).map b
  t_comm : ∀ u : LB.Gen (LB.LinComb D.P.L (rosatiφ D.P.A b' b) rosatiε), u.IsGen →
    LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (zero2 D.P.A)) (LB.oneGen D.P.L) →
    ∀ χ : D.X, LB.Gen.Corr D.P.L _ _ _ _
      (LB.pullGen D.P.L _ _ (g.t χ)
        ((Over.map (thick R I e)).map ((Over.pullback (thick R I e)).map f)).left)
      (LB.mulGen D.P.L _ _ _ _ (g.t (σ χ))
        (LB.pullGen D.P.L _ _ u (lift (toUnit _ ≫ D.c χ) g.pG).left))

structure IsOLinear (O : Type) [Ring O] [StarRing O] {D : DegData R I} [Module O D.toPre.X]
    {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
    {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
    (U : UnifPre I D A G) (ιD : D.OAct O) (ιA : A.OAct O) (ιG : RingAct G O) : Prop where
  gen_comm : ∀ a : O,
    (Over.pullback (jK R)).map (ιG.act a) ≫ U.gen.hom = U.gen.hom ≫ ιA.act a
  gt_comm : ∀ (a : O) (e : ℕ),
    GtCommutes (U.gt e) (ιG.act a) (ιD.onB.act a) (ιD.onB.act (star a)) (fun χ => star a • χ)

section Basic₂

variable {D : DegPre R} {e : ℕ} {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
  [IsCommMonObj G] (g : GtCoord I D e G) {f : G ⟶ G} {b : D.P.A ⟶ D.P.A}

end Basic₂

end GlobalTheory.IndefiniteRowSideFullHecke.OLinearMaps
