import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.GenericFiberGluing.SemistableCompleteSplit
import Development.AbelianVarietyTheory.BlockTheory.AbelianSchemeLaw.SemiAbelianModels

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.Compare.AbelianSchemeTorusCompare

open GlobalTheory.IndefiniteRowSideFullHecke.SemiAbelianModels

def torusExtOf {k : Type} [Field k] {T G B : Over (Spec (CommRingCat.of k))}
    [GrpObj T] [GrpObj G] [GrpObj B] {i : T ⟶ G} {q : G ⟶ B} (h : IsExtensionByTorus i q) :
    TorusExt G where
  B := B
  isAbelian := h.2.1
  q := q
  q_hom := h.2.2.2.1
  q_flat := h.2.2.2.2.1
  q_surjective := h.2.2.2.2.2.1
  q_quasiCompact := h.2.2.2.2.2.2.1
  T₀ := T
  isTorus := h.1
  i := i
  i_hom := h.2.2.1
  isKernel := h.2.2.2.2.2.2.2

theorem isAbelianScheme_of_iso {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B]
    (e : A ≅ B) (he : IsMonHom e.hom) (hB : IsAbelianScheme B) : IsAbelianScheme A := by
  have hw : A.hom = e.hom.left ≫ B.hom := (Over.w e.hom).symm
  have hiso : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget S).map e.hom))
  have := hB.comm
  have := hB.smooth
  have := hB.proper
  have := hB.geomConnected
  refine ⟨⟨?_⟩, ?_, ?_, ?_⟩
  · rw [← cancel_mono e.hom, Category.assoc, IsMonHom.mul_hom e.hom,
      ← BraidedCategory.braiding_naturality_assoc, IsCommMonObj.mul_comm]
  · rw [hw]; infer_instance
  · rw [hw]; infer_instance
  · rw [hw]
    have hbc : MorphismProperty.IsStableUnderBaseChange (C := Scheme.{0})
        @GeometricallyConnected := inferInstance
    have hri : MorphismProperty.RespectsIso (C := Scheme.{0}) @GeometricallyConnected :=
      MorphismProperty.IsStableUnderBaseChange.respectsIso
    exact (MorphismProperty.cancel_left_of_respectsIso @GeometricallyConnected _ _).2 this

end GlobalTheory.Compare.AbelianSchemeTorusCompare
