import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.SplitTori.SplitTorusAff
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj

namespace ReciprocityTheory.ChartRestriction.G.Semi

noncomputable abbrev fieldBaseChange (k Ω : Type u) [Field k] [CommRing Ω] [Algebra k Ω]
    (T : Over (Spec (.of k))) : Over (Spec (.of Ω)) :=
  (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))).obj T

structure IsTorus {k : Type u} [Field k] (T : Over (Spec (.of k))) [GrpObj T] : Prop where
  comm : IsCommMonObj T
  finiteType : LocallyOfFiniteType T.hom
  quasiCompact : QuasiCompact T.hom
  splits : ∃ (Ω : Type u) (_ : Field Ω) (_ : Algebra k Ω)
    (X : Type u) (_ : AddCommGroup X) (_ : Module.Free ℤ X) (_ : Module.Finite ℤ X)
    (e : fieldBaseChange k Ω T ≅ splitTorus (Spec (.of Ω)) X), IsMonHom e.hom

end ReciprocityTheory.ChartRestriction.G.Semi
