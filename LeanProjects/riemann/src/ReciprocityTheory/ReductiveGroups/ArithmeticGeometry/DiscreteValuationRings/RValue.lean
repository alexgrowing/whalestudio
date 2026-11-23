import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullGen

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi IsLocalRing

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  (D : DegData V (maximalIdeal V)) (F : Type) [Field F] [Algebra (FractionRing V) F]
  {O : Type} [CommRing O] [StarRing O] [Module O D.toPre.X]

def rFac (oa : D.toPre.OAct O) (a : O)
    (uR : LB.Gen (LB.LinComb D.toPre.P.L (rosatiφ D.toPre.P.A (oa.onB.act (star a)) (oa.onB.act a)) rosatiε))
    (χ : D.toPre.X) :=
  LB.pullGen D.toPre.P.L _ _ uR (lift (cPB D F χ) (DegPre.prB D.toPre F)).left

def zc (mu : D.toPre.X) : (TF (R := V) F).left ⟶ (DegPre.BF D.toPre F).left :=
  (lift (𝟙 _) (toUnit _ ≫ D.toPre.c mu) : TF (R := V) F ⟶ DegPre.BF D.toPre F).left

end ReciprocityTheory.ChartRestriction.G.DVR
