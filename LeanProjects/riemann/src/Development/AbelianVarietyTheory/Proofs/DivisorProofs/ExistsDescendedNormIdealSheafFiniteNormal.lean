import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NonUnitAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationTransferModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormIdeal
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FamIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFieldStalkImageOfGenericPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionsIsFractionRingStalkImageOfGenericPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalFunctionFieldStalkImageGenericPStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharZeroStalkImageOfGenericPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdealSheafDataOfIsClopenFamilyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormCoeffIdealFamilyMapBasicOpenStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormCoefficientIdealFamilyEqTopOfDisjointStatement

open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LocM

namespace GlobalTheory.NormSheafDescent

theorem descendedIdealSheaf_exists : ∀ (Y Z : Scheme.{0}) (π : Y ⟶ Z) [IsFinite π], IsIntegral Y → IsLocallyNoetherian Y →
    GlobalTheory.IsNormalScheme Y → GlobalTheory.IsNormalScheme Z → IsOpen (Set.range π) → CharZero Γ(Y, ⊤) →
    ∀ I : Y.IdealSheafData, ∃ (K L : Type) (_ : Field K) (_ : Field L) (_ : Algebra K L) (_ : FiniteDimensional K L),
      CharZero K ∧ ∃ J : Z.IdealSheafData, (∀ x ∈ J.support, ∃ y ∈ I.support, π y = x) ∧
      ∀ U : Z.affineOpens, (U : Set Z) ⊆ Set.range π → (U : Set Z).Nonempty →
        ∃ (_ : Algebra Γ(Z, U) K) (_ : Algebra Γ(Y, π ⁻¹ᵁ U.1) L),
          IsDomain Γ(Z, U) ∧ IsIntegrallyClosed Γ(Z, U) ∧ IsDomain Γ(Y, π ⁻¹ᵁ U.1) ∧ (π.app U.1).hom.Finite ∧
          IsFractionRing Γ(Z, U) K ∧ IsFractionRing Γ(Y, π ⁻¹ᵁ U.1) L ∧
          (algebraMap K L).comp (algebraMap Γ(Z, U) K) = (algebraMap Γ(Y, π ⁻¹ᵁ U.1) L).comp (π.app U.1).hom ∧
          J.ideal U = GlobalTheory.NormSheaf.normIdeal Γ(Z, U) K L Γ(Y, π ⁻¹ᵁ U.1) (I.ideal ⟨π ⁻¹ᵁ U.1, U.2.preimage π⟩) := by
  intro Y Z π _ hY _ _ hnZ hW hchar I
  have hK := GlobalTheory.T.isField_stalk_imageOfGenericPoint Y Z π hW
  have hfd := GlobalTheory.T.finiteDimensional_functionField_stalk_imageGenericPoint Y Z π hK
  letI := GlobalTheory.NormSheafDescent.fieldK π hK
  letI := GlobalTheory.NormSheafDescent.algKL π
  have hcl : IsClosed (Set.range π) := π.isClosedMap.isClosed_range
  obtain ⟨J, hJ, hJs⟩ := GlobalTheory.T.exists_idealSheafData_of_isClopen_family Z (Set.range π) ⟨hcl, hW⟩ (GlobalTheory.NormSheafDescent.famIdeal π hK hfd I)
    (fun U f hU => GlobalTheory.T.normCoeffIdealFamily_map_basicOpen Y Z π hK hfd I U f hU)
  have hgen : ∀ (U : Z.Opens) (x : Z), x ∈ U → x ∈ Set.range π →
      GlobalTheory.NormSheafDescent.genPt π ∈ U := by
    rintro U _ hx ⟨y, rfl⟩
    exact ((genericPoint_specializes y).map π.continuous).mem_open U.isOpen hx
  refine ⟨Z.presheaf.stalk (GlobalTheory.NormSheafDescent.genPt π), Y.functionField, inferInstance, inferInstance,
    inferInstance, hfd, GlobalTheory.T.charZero_stalk_imageOfGenericPoint Y Z π hchar hK, J, ?_, ?_⟩
  · intro x hx
    by_contra hne
    push_neg at hne
    have hxW := hJs hx
    have hS : IsClosed (π '' (I.support : Set Y)) := π.isClosedMap _ I.support.isClosed
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUsub⟩ := Z.isBasis_affineOpens.exists_subset_of_mem_open
      (show x ∈ (π '' (I.support : Set Y))ᶜ ∩ Set.range π from ⟨fun ⟨y, hy, e⟩ => hne y hy e, hxW⟩)
      (hS.isOpen_compl.inter hW)
    have htop := GlobalTheory.T.normCoefficientIdealFamily_eq_top_of_disjoint Y Z π hK hfd I ⟨U, hU⟩ (fun y hy hyU => (hUsub hyU).1 ⟨y, hy, rfl⟩)
    have hx' := (Scheme.IdealSheafData.mem_support_iff_of_mem (U := ⟨U, hU⟩) hxU).mp hx
    rw [hJ ⟨U, hU⟩ (fun z hz => (hUsub hz).2), htop] at hx'
    exact (Scheme.mem_zeroLocus_iff _ _ _).mp hx' 1 Submodule.mem_top (by simpa using hxU)
  · rintro U hUW ⟨x, hxU⟩
    have h := hgen U.1 x hxU (hUW hxU)
    obtain ⟨hdom, hfr⟩ := GlobalTheory.T.sections_isFractionRing_stalk_imageOfGenericPoint Y Z π U.1 U.2 hUW h
    letI := GlobalTheory.NormSheafDescent.algAK π U.1 h
    letI := GlobalTheory.NormSheafDescent.algBL π U.1 h
    haveI : Nonempty (π ⁻¹ᵁ U.1) := ⟨⟨genericPoint Y, h⟩⟩
    refine ⟨inferInstance, inferInstance, hdom, GlobalTheory.IsNormalScheme.isIntegrallyClosed_of_isAffineOpen U.2,
      inferInstance, ?_, hfr, ?_, ?_, ?_⟩
    · exact π.finite_app U.1 U.2
    · exact functionField_isFractionRing_of_isAffineOpen Y _ (U.2.preimage π)
    · ext a
      exact Scheme.Hom.germ_stalkMap_apply π U.1 (genericPoint Y) h a
    · rw [hJ U hUW]
      simp only [GlobalTheory.NormSheafDescent.famIdeal, dif_pos h]

end GlobalTheory.NormSheafDescent
