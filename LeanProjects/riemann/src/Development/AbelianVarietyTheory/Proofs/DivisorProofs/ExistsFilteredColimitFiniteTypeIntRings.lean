import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.FiniteTypeColimit

noncomputable def diagram (A : CommRingCat.{0}) : Finset A ⥤ CommRingCat.{0} where
  obj t := CommRingCat.of (Algebra.adjoin ℤ (t : Set A))
  map {s t} h := CommRingCat.ofHom
    (Subalgebra.inclusion (Algebra.adjoin_mono (Finset.coe_subset.2 (leOfHom h)))).toRingHom
  map_id _ := rfl
  map_comp _ _ := rfl

noncomputable def inclusions (A : CommRingCat.{0}) : diagram A ⟶ (Functor.const (Finset A)).obj A where
  app t := CommRingCat.ofHom (Algebra.adjoin ℤ (t : Set A)).val.toRingHom
  naturality _ _ _ := rfl

noncomputable def isColimit (A : CommRingCat.{0}) : IsColimit (Cocone.mk A (inclusions A)) := by
  classical
  haveI : ReflectsColimit (diagram A) (forget CommRingCat.{0}) :=
    reflectsColimit_of_reflectsIsomorphisms _ _
  refine isColimitOfReflects (forget CommRingCat.{0}) ?_
  refine Types.FilteredColimit.isColimitOf' _ _ (fun x => ?_) (fun i x y hxy => ?_)
  · exact ⟨{x}, ⟨x, Algebra.subset_adjoin (by simp)⟩, rfl⟩
  · have : x = y := Subtype.ext hxy
    exact ⟨i, 𝟙 i, by rw [this]⟩

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct in
theorem _root_.GlobalTheory.FiniteTypeColimit.finiteType (A : CommRingCat.{0}) (t : Finset A) :
    Algebra.FiniteType ℤ ((_root_.GlobalTheory.FiniteTypeColimit.diagram A).obj t) := by
  have h : (Algebra.adjoin ℤ (t : Set A)).FG := Subalgebra.fg_adjoin_finset t
  have := (Subalgebra.fg_iff_finiteType _).1 h
  change Algebra.FiniteType ℤ (CommRingCat.of (Algebra.adjoin ℤ (t : Set A)))
  convert this

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct in

theorem _root_.GlobalTheory.FiniteTypeColimit.exists_filtered_colimit_finiteType : ∀ A : CommRingCat.{0},
    ∃ (J : Type) (_ : SmallCategory J) (_ : IsFiltered J) (D : J ⥤ CommRingCat.{0})
      (ι : D ⟶ (Functor.const J).obj A),
      Nonempty (IsColimit (Cocone.mk A ι)) ∧ ∀ j, Algebra.FiniteType ℤ (D.obj j) :=
  fun A => ⟨Finset A, inferInstance, inferInstance, _root_.GlobalTheory.FiniteTypeColimit.diagram A,
    _root_.GlobalTheory.FiniteTypeColimit.inclusions A, ⟨_root_.GlobalTheory.FiniteTypeColimit.isColimit A⟩,
    _root_.GlobalTheory.FiniteTypeColimit.finiteType A⟩

end GlobalTheory.FiniteTypeColimit
