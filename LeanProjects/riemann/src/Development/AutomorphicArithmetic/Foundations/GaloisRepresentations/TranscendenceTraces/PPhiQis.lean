import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PhiExact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChosenInjectiveResolutionEtaleSheafPropertiesStatement

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

private theorem single_key {R : Type} [CommRing R] (Φ : Shv R ⥤ Shv R) [Φ.Additive] (F : Shv R) :
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (Φ.obj F)).inv ≫
      ((HomologicalComplex.singleMapHomologicalComplex Φ (ComplexShape.up ℤ) 0).inv.app F).f 0 =
    Φ.map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).inv := by
  rw [HomologicalComplex.singleMapHomologicalComplex_inv_app_self]
  simp
  rfl

theorem UpperTheory.Gal.TranscendenceTraces.phiQis_of :
    PhiQis := by
  intro R _ Φ _ hΦ F
  obtain ⟨-, -, -, hq, hι, -, -, -⟩ := GlobalTheory.T.chosenInjectiveResolution_etaleSheaf_properties R F
  haveI : Φ.PreservesHomology := (Φ.exact_tfae.out 1 2).1 hΦ
  let e := (HomologicalComplex.singleMapHomologicalComplex Φ (ComplexShape.up ℤ) 0).app F
  let φ : (HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) 0 ⋙
      Φ.mapHomologicalComplex (ComplexShape.up ℤ)).obj F ⟶
      (Φ.mapHomologicalComplex (ComplexShape.up ℤ)).obj (res R F) :=
    (Φ.mapHomologicalComplex (ComplexShape.up ℤ)).map (resAug F)
  haveI hφ : QuasiIso φ :=
    (inferInstance : QuasiIso ((Φ.mapHomologicalComplex (ComplexShape.up ℤ)).map (resAug F)))
  haveI he : QuasiIso e.inv := inferInstance
  refine ⟨e.inv ≫ φ, quasiIso_comp e.inv φ, ?_⟩
  erw [HomologicalComplex.comp_f]
  rw [← Category.assoc]
  erw [single_key]
  exact (Φ.map_comp _ _).symm.trans (congrArg Φ.map hι)
