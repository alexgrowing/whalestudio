import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC.FilteredElements

instance forgetPreservesSmall :
    PreservesFilteredColimitsOfSize.{0, 0} (forget AddCommGrpCat.{1}) :=
  preservesFilteredColimitsOfSize_shrink.{0, 1, 0, 1} _

theorem preservesFilteredColimits_iff_elements :
    ∀ (T : Type 1) [Category.{0} T] (N : T ⥤ AddCommGrpCat.{1}), PreservesFilteredColimitsOfSize.{0, 0} N ↔ ∀ (J : Type) [SmallCategory J] [IsFiltered J] (D : J ⥤ T) (c : Cocone D), IsColimit c → (∀ x : N.obj c.pt, ∃ j y, N.map (c.ι.app j) y = x) ∧ ∀ j (y : N.obj (D.obj j)), N.map (c.ι.app j) y = 0 → ∃ (k : J) (f : j ⟶ k), N.map (D.map f) y = 0 := by
  intro T _ N
  constructor
  · intro hN J _ _ D c hc
    have h1 : IsColimit (N.mapCocone c) := isColimitOfPreserves N hc
    have h2 : IsColimit ((forget AddCommGrpCat.{1}).mapCocone (N.mapCocone c)) :=
      isColimitOfPreserves (forget AddCommGrpCat.{1}) h1
    refine ⟨fun x => ?_, fun j y hy => ?_⟩
    · obtain ⟨j, y, hy⟩ := Types.jointly_surjective_of_isColimit h2 x
      exact ⟨j, y, hy⟩
    · have h3 := (Types.FilteredColimit.isColimit_eq_iff' h2 y 0).1 (by
        change N.map (c.ι.app j) y = N.map (c.ι.app j) 0
        rw [hy, map_zero])
      obtain ⟨k, f, hf⟩ := h3
      refine ⟨k, f, ?_⟩
      have : N.map (D.map f) y = N.map (D.map f) 0 := hf
      rw [this, map_zero]
  · intro h
    constructor
    intro J _ _
    constructor
    intro D
    constructor
    intro c hc
    obtain ⟨hs, hi⟩ := h J D c hc
    haveI : ReflectsColimit (D ⋙ N) (forget AddCommGrpCat.{1}) :=
      reflectsColimit_of_reflectsIsomorphisms _ _
    refine ⟨isColimitOfReflects (forget AddCommGrpCat.{1}) ?_⟩
    refine Types.FilteredColimit.isColimitOf' _ _ (fun x => ?_) (fun i (x y : N.obj (D.obj i)) hxy => ?_)
    · obtain ⟨j, y, hy⟩ := hs x
      exact ⟨j, y, hy.symm⟩
    · have hxy' : N.map (c.ι.app i) (x - y) = 0 := by
        have : (N.map (c.ι.app i)).hom x = (N.map (c.ι.app i)).hom y := hxy
        change (N.map (c.ι.app i)).hom (x - y) = 0
        rw [AddMonoidHom.map_sub, this, sub_self]
      obtain ⟨k, f, hf⟩ := hi i (x - y) hxy'
      refine ⟨k, f, ?_⟩
      change (N.map (D.map f)).hom x = (N.map (D.map f)).hom y
      have hf' : (N.map (D.map f)).hom (x - y) = 0 := hf
      rw [AddMonoidHom.map_sub, sub_eq_zero] at hf'
      exact hf'

end GlobalTheory.EtC.FilteredElements
