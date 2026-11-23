import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendScalarsUliftHomAdditive
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafComplexMappingConeAcyclicOfQuasiIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatSectionsOfInjectiveZmodEtaleSheafStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistSheafIsLocallyFlatStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AcyclicExtendScalarsZmodOfFlatBoundedBelowStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyFlatEtaleSheafBiprodStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyFlatEtaleSheafIsoAndZeroStatement

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.ExtQis

theorem quasiIso_of_mappingCone_acyclic {𝒜 : Type*} [Category 𝒜] [Abelian 𝒜]
    {K L : CochainComplex 𝒜 ℤ} (u : K ⟶ L) (h : (CochainComplex.mappingCone u).Acyclic) : QuasiIso u := by
  rw [← HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic] at h
  have hu : HomotopyCategory.quasiIso 𝒜 (ComplexShape.up ℤ)
      ((HomotopyCategory.quotient 𝒜 (ComplexShape.up ℤ)).map u) := by
    rw [HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic]
    exact ((HomotopyCategory.subcategoryAcyclic 𝒜).trW_iff_of_distinguished _
      (HomotopyCategory.mappingCone_triangleh_distinguished u)).2 h
  rwa [HomotopyCategory.quotient_map_mem_quasiIso_iff] at hu

theorem flatS_cone (Q : ℕ) [NeZero Q] (F : Shv (ZMod Q)) (hF : FlatS F) (n : ℤ) :
    FlatS ((mappingCone (resAug F)).X n) := by
  obtain ⟨hiso, hzero⟩ := GlobalTheory.T.isLocallyFlatEtaleSheaf_iso_and_zero (ZMod Q)
  refine hiso (HomologicalComplex.homotopyCofiber.XIsoBiprod (resAug F) n (n + 1) rfl).symm
    (GlobalTheory.T.isLocallyFlatEtaleSheaf_biprod _ _ _ ?_ ?_)
  · by_cases h : n + 1 = 0
    · exact hiso (HomologicalComplex.singleObjXIsoOfEq (ComplexShape.up ℤ) 0 F (n + 1) h).symm hF
    · exact hzero _ (HomologicalComplex.isZero_single_obj_X _ _ _ _ h)
  · haveI : Injective ((res (ZMod Q) F).X n) :=
      (inferInstance : Injective ((injectiveResolution F).cochainComplex.X n))
    exact (GlobalTheory.T.flat_sections_of_injective_zmodEtaleSheaf Q _).2

theorem quasiIso_extAug : ∀ (Q q : ℕ) [NeZero Q] (hq : q ∣ Q) (i : ℤ),
    QuasiIso (extAug (ZMod.castHom hq (ZMod q)) (tw Q i)) := by
  intro Q q _ hq i
  have hq' : QuasiIso (resAug (tw Q i)) := (inferInstance : QuasiIso (injectiveResolution (tw Q i)).ι')
  have hK : (mappingCone (resAug (tw Q i))).Acyclic := GlobalTheory.mappingCone_acyclic_of_quasiIso _
  haveI : (res (ZMod Q) (tw Q i)).IsStrictlyGE 0 :=
    (inferInstance : (injectiveResolution (tw Q i)).cochainComplex.IsStrictlyGE 0)
  haveI : (mappingCone (resAug (tw Q i))).IsStrictlyGE (-1) := CochainComplex.isStrictlyGE_mappingCone _ 0 0 (-1)
  have hE := GlobalTheory.T.acyclic_extendScalars_zmod_of_flat_boundedBelow Q q hq (mappingCone (resAug (tw Q i))) (-1)
    (flatS_cone Q (tw Q i) (GlobalTheory.T.tateTwistSheaf_isLocallyFlat Q i)) hK
  have hC : (mappingCone (((extSh (ZMod.castHom hq (ZMod q))).mapHomologicalComplex _).map
      (resAug (tw Q i)))).Acyclic := fun n =>
    (hE n).of_iso (CochainComplex.mappingCone.mapHomologicalComplexIso (resAug (tw Q i))
      (extSh (ZMod.castHom hq (ZMod q))))
  have h1 := quasiIso_of_mappingCone_acyclic _ hC
  have h2 : QuasiIso ((HomologicalComplex.singleMapHomologicalComplex (extSh (ZMod.castHom hq (ZMod q)))
      (ComplexShape.up ℤ) 0).inv.app (tw Q i)) := quasiIso_of_isIso _
  exact quasiIso_comp (hφ := h2) (hφ' := h1) _ _

end GlobalTheory.EtC.ExtQis

end
