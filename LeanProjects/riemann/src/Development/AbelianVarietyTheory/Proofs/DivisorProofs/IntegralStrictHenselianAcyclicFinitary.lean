import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSepClosedResidueFieldOfModuleFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AcycFOfPiShStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyFilteredColimitRingsFinitaryStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC.IntAcyc

variable (A B : Type) [CommRing A] [CommRing B] [Algebra A B]

def finDiag : Finset B ⥤ CommRingCat.{0} where
  obj t := CommRingCat.of (Algebra.adjoin A (t : Set B))
  map {t u} h := CommRingCat.ofHom
    (Subalgebra.inclusion (Algebra.adjoin_mono (Finset.coe_subset.2 h.le))).toRingHom
  map_id _ := by ext; rfl
  map_comp _ _ := by ext; rfl

def finCocone : Cocone (finDiag A B) where
  pt := CommRingCat.of B
  ι := { app := fun t => CommRingCat.ofHom (Algebra.adjoin A (t : Set B)).val.toRingHom
         naturality := fun _ _ _ => by ext; rfl }

def finCoconeIsColimit : IsColimit (finCocone A B) := by
  classical
  haveI : ReflectsColimitsOfShape (Finset B) (forget CommRingCat.{0}) :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  refine isColimitOfReflects (forget CommRingCat.{0})
    (Types.FilteredColimit.isColimitOf _ ((forget CommRingCat.{0}).mapCocone (finCocone A B)) ?_ ?_)
  · intro x
    exact ⟨{x}, ⟨x, Algebra.subset_adjoin (Finset.mem_coe.2 (Finset.mem_singleton_self x))⟩, rfl⟩
  · intro i j xi xj h
    refine ⟨i ⊔ j, homOfLE le_sup_left, homOfLE le_sup_right, ?_⟩
    apply Subtype.ext
    exact h

theorem finite_finDiag [Algebra.IsIntegral A B] (t : Finset B) :
    Module.Finite A (Algebra.adjoin A (t : Set B)) :=
  Algebra.finite_adjoin_of_finite_of_isIntegral t.finite_toSet
    (fun x _ => Algebra.IsIntegral.isIntegral x)

end GlobalTheory.EtC.IntAcyc
end

namespace GlobalTheory.EtC.IntAcyc

theorem acycF_of_isIntegral : ∀ (R : Type) [CommRing R] (F : Shv R), Finitary F →
    ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [Algebra.IsIntegral A B],
      SH A → AcycF R (sp B) F := by
  classical
  intro R _ F hF A B _ _ _ _ hA
  obtain ⟨hHens, hSep⟩ := hA
  intro n hn
  suffices h : ∀ x : H R (sp B) F n, x = 0 from ⟨fun x y => by rw [h x, h y]⟩
  intro x
  obtain ⟨j, y, hy⟩ := (GlobalTheory.T.etaleCohomology_filteredColimit_rings_finitary R F hF (Finset B) (finDiag A B) (finCocone A B)
    (finCoconeIsColimit A B) n).1 x
  haveI := finite_finDiag A B j
  obtain ⟨ι, hι, T, hT, hAl, e, hH, hS⟩ :=
    GlobalTheory.finite_algebra_strictly_henselian_pi A (Algebra.adjoin A (j : Set B))
  have hac : AcycF R (sp ((finDiag A B).obj j)) F :=
    GlobalTheory.T.acycF_of_pi_sh' R F ι T ((finDiag A B).obj j) ⟨e.toRingEquiv⟩ (fun i => ⟨hH i, (hS i).1⟩)
  haveI := hac n hn
  have hy0 : y = 0 := Subsingleton.elim _ _
  rw [← hy, hy0]
  exact map_zero _

end GlobalTheory.EtC.IntAcyc
