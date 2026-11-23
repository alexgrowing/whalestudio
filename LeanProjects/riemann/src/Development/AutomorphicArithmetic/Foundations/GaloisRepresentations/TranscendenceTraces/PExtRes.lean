import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PhiExact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChosenInjectiveResolutionEtaleSheafPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendChainMapAlongQuasiIsoKInjectiveStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.extRes_of :
    ExtRes := by
  intro R _ F G T ε _
  obtain ⟨hKI, -, hGE, -, hι, -⟩ := GlobalTheory.T.chosenInjectiveResolution_etaleSheaf_properties R G
  haveI := hKI
  haveI := hGE
  have key := GlobalTheory.T.extend_chainMap_along_quasiIso_kInjective R F T (res R G) ε
  refine ⟨fun a => ?_, fun m m' h U i n k hin hnk y hy => ?_⟩
  · obtain ⟨m, hm⟩ := key.1 ((CochainComplex.singleFunctor (Shv R) 0).map a ≫ resAug G)
    refine ⟨m, ?_⟩
    have h0 : ε.f 0 ≫ m.f 0 = ((CochainComplex.singleFunctor (Shv R) 0).map a).f 0 ≫ (resAug G).f 0 := by
      rw [← HomologicalComplex.comp_f, hm, HomologicalComplex.comp_f]
    rw [h0, ← hι]
    change (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).inv ≫
        ((HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) 0).map a).f 0 ≫ (resAug G).f 0 =
      a ≫ (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 G).inv ≫ (resAug G).f 0
    rw [HomologicalComplex.single_map_f_self]
    exact (congrArg (_ ≫ ·) (Category.assoc _ _ _)).trans
      ((Iso.inv_hom_id_assoc _ _).trans (Category.assoc _ _ _))
  · have hε : ε ≫ m = ε ≫ m' := by
      refine HomologicalComplex.from_single_hom_ext (j := 0) ?_
      rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f]
      exact (Iso.cancel_iso_inv_left (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F) _ _).1 h
    obtain ⟨H⟩ := key.2 m m' hε
    have hc := H.comm n
    rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel n k from hnk),
      prevD_eq _ (show (ComplexShape.up ℤ).Rel i n from hin)] at hc
    have e1 : Sec.map (T.d n k ≫ H.hom k n) y = 0 := by
      change Sec.map (H.hom k n) (Sec.map (T.d n k) y) = 0
      rw [hy]
      exact map_zero _
    have e2 : Sec.map (H.hom n i ≫ (res R G).d i n) y = Sec.map ((res R G).d i n) (Sec.map (H.hom n i) y) := rfl
    have e3 : ∀ {A B : Shv R} (f g : A ⟶ B) (x : Sec A U), Sec.map (f + g) x = Sec.map f x + Sec.map g x :=
      fun _ _ _ => rfl
    refine ⟨Sec.map (H.hom n i) y, ?_⟩
    rw [hc, e3, e3, e1, e2, zero_add, add_sub_cancel_right]
