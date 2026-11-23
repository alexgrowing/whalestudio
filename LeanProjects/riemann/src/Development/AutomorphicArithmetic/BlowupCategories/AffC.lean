import Development.AutomorphicArithmetic.BlowupCategories.SpanScale

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC UpperTheory.Pbf

namespace UpperTheory.Blow

def affD : CommRingCat.{0} ⥤ Type where
  obj A := A
  map f := TypeCat.ofHom f.hom
  map_id _ := rfl
  map_comp _ _ := rfl

def affC : Act where
  D := affD
  G := (Functor.const _).obj (GrpCat.of PUnit.{1})
  smul _ _ x := x
  one_smul _ _ := rfl
  mul_smul _ _ _ _ := rfl
  nat _ _ _ := rfl

end UpperTheory.Blow
end
