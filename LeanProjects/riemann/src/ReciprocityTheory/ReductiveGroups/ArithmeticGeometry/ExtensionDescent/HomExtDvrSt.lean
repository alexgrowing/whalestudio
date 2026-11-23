import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.GenericFiberGluing.SemistableReductionPlusSplit
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.Out

open Semi

def HomExtDvrSt : Prop :=
  ∀ (T : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T]
    (G G' : Over (Spec (CommRingCat.of T))) [GrpObj G] [GrpObj G'],
    IsSemiAbelian G → IsSemiAbelian G' →
    ∀ φ : genFibre T G ⟶ genFibre T G', IsMonHom φ →
      ∃! ψ : G ⟶ G', IsMonHom ψ ∧ (Over.pullback (specMap T (FractionRing T))).map ψ = φ

structure Laws7 : Prop where
  homExtDvr : HomExtDvrSt

end ReciprocityTheory.ChartRestriction.G.Out
