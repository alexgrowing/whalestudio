import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.SplitTori.SplitTorusAff
import Mathlib.AlgebraicGeometry.Morphisms.Proper

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj

namespace ReciprocityTheory.ChartRestriction.G.Semi

variable {S : Scheme.{u}}

class IsAbelianScheme (A : Over S) [GrpObj A] : Prop where
  comm : IsCommMonObj A
  smooth : Smooth A.hom
  proper : IsProper A.hom
  geomConnected : GeometricallyConnected A.hom

structure TorusExtension {K : Type u} [Field K] (G : Over (Spec (.of K))) [GrpObj G] where

  X : Type u
  [addCommGroup : AddCommGroup X]
  [free : Module.Free ℤ X]
  [finite : Module.Finite ℤ X]

  B : Over (Spec (.of K))
  [grpB : GrpObj B]
  isAbelian : IsAbelianScheme B

  q : G ⟶ B
  q_hom : IsMonHom q
  q_flat : Flat q.left
  q_surjective : Surjective q.left
  q_quasiCompact : QuasiCompact q.left

  i : splitTorus (Spec (.of K)) X ⟶ G
  i_hom : IsMonHom i

  isKernel : IsPullback i (toUnit _) q (η : 𝟙_ _ ⟶ B)

class IsSemiAbelian (G : Over S) [GrpObj G] : Prop where
  comm : IsCommMonObj G
  smooth : Smooth G.hom
  separated : IsSeparated G.hom
  quasiCompact : QuasiCompact G.hom
  geomConnected : GeometricallyConnected G.hom
  fibres : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (p : Spec (.of Ω) ⟶ S),
    Nonempty (TorusExtension ((Over.pullback p).obj G))

end ReciprocityTheory.ChartRestriction.G.Semi
