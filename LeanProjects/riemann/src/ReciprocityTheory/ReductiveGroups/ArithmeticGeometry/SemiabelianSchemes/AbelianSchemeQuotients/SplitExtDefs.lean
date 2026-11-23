import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj

namespace ReciprocityTheory.ChartRestriction.G.Semi

structure SplitExt (S : Scheme.{u}) where

  B : Over S
  [grpB : GrpObj B]
  isAbelian : IsAbelianScheme B

  X : Type u
  [addCommGroup : AddCommGroup X]
  [free : Module.Free ℤ X]
  [finite : Module.Finite ℤ X]

  O : X → RigLB B

  addIso : ∀ χ χ' : X, ∃ t : LB.Iso (O χ').L (LB.div (O (χ + χ')).L (O χ).L), t.IsGen

  zeroTriv : ∃ t : LB.Gen (O 0).L, t.IsGen

  primitive : ∀ χ : X, ∃ t : LB.Gen (abelian₂ B (O χ).L), t.IsGen

attribute [instance] SplitExt.grpB SplitExt.addCommGroup

end ReciprocityTheory.ChartRestriction.G.Semi
