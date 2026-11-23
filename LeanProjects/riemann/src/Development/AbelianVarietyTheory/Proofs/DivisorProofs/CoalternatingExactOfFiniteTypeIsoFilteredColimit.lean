import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleFaithfullyFlatFilteredColimitFiniteTypeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsColimitLeftFuncAndCechConerveLevels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechConerveObjFiniteTypeInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WExactColimit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WExactCongr
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

noncomputable def coAugNat {J : Type} [SmallCategory J] (D : J ⥤ Arrow CommRingCat.{0}) :
    (D ⋙ Arrow.leftFunc) ⋙ CosimplicialObject.const CommRingCat.{0} ⟶ D ⋙ CosimplicialObject.cechConerve where
  app j := coAug (D.obj j).hom
  naturality i j f := by
    have h := (CosimplicialObject.augmentedCechConerve.map (D.map f)).w
    exact h

theorem wExact_of_finiteType_iso (N M : CommRingCat.{0} ⥤ AddCommGrpCat.{1}) (ε : N ⟶ M)
    (hN : PreservesFilteredColimitsOfSize.{0, 0} N)
    (hε : ∀ A : CommRingCat.{0}, Algebra.FiniteType ℤ A → IsIso (ε.app A))
    (hM : ∀ (A B : CommRingCat.{0}) (g : A ⟶ B), EtFF g → WExact M (coAug g)) :
    ∀ (A B : CommRingCat.{0}) (g : A ⟶ B), EtFF g → WExact N (coAug g) := by
  intro A B g hg
  obtain ⟨J, _, _, D, ι, ⟨hc⟩, hD⟩ := GlobalTheory.T.etaleFaithfullyFlat_filtered_colimit_finiteType A B g hg
  obtain ⟨⟨hU⟩, hX⟩ := GlobalTheory.EtC.isColimit_leftFunc_and_cechConerve_levels J D _ hc
  refine GlobalTheory.EtC.WExactColim.wExact_colimit CommRingCat.{0} N hN J (D ⋙ Arrow.leftFunc)
    (D ⋙ CosimplicialObject.cechConerve) (coAugNat D) (Arrow.leftFunc.mapCocone (Cocone.mk (Arrow.mk g) ι))
    (CosimplicialObject.cechConerve.mapCocone (Cocone.mk (Arrow.mk g) ι)) (coAug g) hU (fun k => hX k) ?_ ?_
  · intro j
    have h := (CosimplicialObject.augmentedCechConerve.map (ι.app j)).w
    exact h.symm
  · intro j
    obtain ⟨hj, hl, hr⟩ := hD j
    refine (GlobalTheory.EtC.wExact_congr CommRingCat.{0} _ _ (coAug (D.obj j).hom) N M ε (hε _ hl) (fun k => hε _ ?_)).2
      (hM _ _ _ hj)
    exact GlobalTheory.cechConerve_obj_finiteType_int _ _ (D.obj j).hom hr k

end GlobalTheory.EtC
