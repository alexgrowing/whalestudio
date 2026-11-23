import Mathlib
import Development.EtaleCohomology.EtaleSheaves.LeafKillCut
import Development.EtaleCohomology.EtaleSheaves.ProperLineCovers.CoverPf
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsProperCurveThroughPoint
import Development.AutomorphicArithmetic.CommutativeAlgebra.ModuleFiniteIntegralClosureFiniteExtPerfect
import Development.AutomorphicArithmetic.CommutativeAlgebra.SmoothOfNormalCurvePerfectField
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.FiniteTypeSectionsOfIsFiniteTypeOverZ
import GroundTheory.ArithmeticGeometry.ToricVarieties.Dimension
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.E4
open GroundTheory.Heights₂.Heights.Model (genericSpecMap)

private theorem objIso {C : Scheme.{0}} [IsIntegral C] (F : Type) [Field F] [Algebra C.functionField F]
    [QuasiCompact (genericSpecMap C F)] [QuasiSeparated (genericSpecMap C F)]
    (U : C.Opens) (hU : IsAffineOpen U) [Nonempty U] [Algebra Γ(C, U) F]
    [IsScalarTower Γ(C, U) C.functionField F] :
    ∃ E : Γ((genericSpecMap C F).normalization, (genericSpecMap C F).fromNormalization ⁻¹ᵁ U) ≅
        CommRingCat.of (integralClosure Γ(C, U) F),
      (genericSpecMap C F).fromNormalization.app U ≫ E.hom =
        CommRingCat.ofHom (algebraMap Γ(C, U) (integralClosure Γ(C, U) F)) := by
  have hη : genericPoint C ∈ U :=
    ((genericPoint_spec C).mem_open_set_iff U.isOpen).mpr (by simpa using ‹Nonempty U›)
  have hmem : genericSpecMap C F (IsLocalRing.closedPoint F) ∈ U := by
    rw [GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model.genericSpecMap_closedPoint]
    exact hη
  have key := GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model.genericSpecMap_app_iso C F U hη hmem
  letI : Algebra Γ(C, U) Γ(Spec (CommRingCat.of F), genericSpecMap C F ⁻¹ᵁ U) :=
    ((genericSpecMap C F).app U).hom.toAlgebra
  let eR := ((Spec (CommRingCat.of F)).presheaf.mapIso (eqToIso
    (Scheme.preimage_eq_top_of_closedPoint_mem _ hmem).symm).op ≪≫
    Scheme.ΓSpecIso (CommRingCat.of F)).commRingCatIsoToRingEquiv
  let eA : Γ(Spec (CommRingCat.of F), genericSpecMap C F ⁻¹ᵁ U) ≃ₐ[Γ(C, U)] F :=
    AlgEquiv.ofRingEquiv (f := eR) fun x => by
      rw [IsScalarTower.algebraMap_apply Γ(C, U) C.functionField F]
      exact congrArg (fun φ => φ.hom x) key
  refine ⟨(genericSpecMap C F).normalizationObjIso hU ≪≫
    eA.mapIntegralClosure.toRingEquiv.toCommRingCatIso, ?_⟩
  rw [(genericSpecMap C F).fromNormalization_app hU]
  rw [Iso.trans_hom, Category.assoc, Iso.inv_hom_id_assoc]
  ext x
  exact eA.commutes x

private theorem isFin {Ω : Type} [Field Ω] [IsAlgClosed Ω] {C : Scheme.{0}} [IsIntegral C]
    (c : C ⟶ Sp Ω) [LocallyOfFiniteType c] (F : Type) [Field F] [Algebra C.functionField F]
    [FiniteDimensional C.functionField F]
    [QuasiCompact (genericSpecMap C F)] [QuasiSeparated (genericSpecMap C F)] :
    IsFinite (genericSpecMap C F).fromNormalization := by
  refine ⟨fun U hU => ?_⟩
  by_cases hN : (U : Set C).Nonempty
  · haveI : Nonempty U := ⟨⟨hN.some, hN.some_mem⟩⟩
    haveI : IsFractionRing Γ(C, U) C.functionField :=
      functionField_isFractionRing_of_isAffineOpen C U hU
    letI : Algebra Ω Γ(C, U) := (GlobalTheory.NormCurve.constHom c U).toAlgebra
    haveI : Algebra.FiniteType Ω Γ(C, U) := GlobalTheory.NormCurve.finiteType_constHom c hU
    letI : Algebra Γ(C, U) F :=
      ((algebraMap C.functionField F).comp (algebraMap Γ(C, U) C.functionField)).toAlgebra
    haveI : IsScalarTower Γ(C, U) C.functionField F := IsScalarTower.of_algebraMap_eq' rfl
    haveI : Module.Finite Γ(C, U) (integralClosure Γ(C, U) F) :=
      UpperTheory.module_finite_integralClosure_finiteExt_perfect Ω Γ(C, U) C.functionField F
    obtain ⟨E, hE⟩ := objIso F U hU
    have h1 : (genericSpecMap C F).fromNormalization.app U =
        CommRingCat.ofHom (algebraMap Γ(C, U) (integralClosure Γ(C, U) F)) ≫ E.inv := by
      rw [← hE, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rw [h1, CommRingCat.hom_comp]
    refine RingHom.Finite.comp (RingHom.Finite.of_surjective _ fun y => ⟨E.hom y, ?_⟩)
      (RingHom.finite_algebraMap.mpr inferInstance)
    simp
  · have hb : U = ⊥ := TopologicalSpace.Opens.ext (Set.not_nonempty_iff_eq_empty.mp hN)
    subst hb
    have hb' : (genericSpecMap C F).fromNormalization ⁻¹ᵁ (⊥ : C.Opens) = ⊥ := by simp
    haveI : Subsingleton Γ((genericSpecMap C F).normalization,
        (genericSpecMap C F).fromNormalization ⁻¹ᵁ (⊥ : C.Opens)) :=
      CommRingCat.subsingleton_of_isTerminal
        ((genericSpecMap C F).normalization.sheaf.isTerminalOfEqEmpty hb')
    exact RingHom.Finite.of_surjective _ fun y => ⟨0, Subsingleton.elim _ _⟩

private theorem stalkClosed {C : Scheme.{0}} [IsIntegral C] (F : Type) [Field F]
    [Algebra C.functionField F] [FiniteDimensional C.functionField F]
    [QuasiCompact (genericSpecMap C F)] [QuasiSeparated (genericSpecMap C F)]
    (y : (genericSpecMap C F).normalization) :
    IsIntegrallyClosed ((genericSpecMap C F).normalization.presheaf.stalk y) := by
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset
    (x := (genericSpecMap C F).fromNormalization y) (U := ⊤) trivial
  haveI : Nonempty U := ⟨⟨_, hxU⟩⟩
  haveI : IsFractionRing Γ(C, U) C.functionField :=
    functionField_isFractionRing_of_isAffineOpen C U hU
  letI : Algebra Γ(C, U) F :=
    ((algebraMap C.functionField F).comp (algebraMap Γ(C, U) C.functionField)).toAlgebra
  haveI : IsScalarTower Γ(C, U) C.functionField F := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsIntegrallyClosed (integralClosure Γ(C, U) F) :=
    integralClosure.isIntegrallyClosedOfFiniteExtension C.functionField
  obtain ⟨E, -⟩ := objIso F U hU
  have hV : IsAffineOpen ((genericSpecMap C F).fromNormalization ⁻¹ᵁ U) :=
    hU.preimage (genericSpecMap C F).fromNormalization
  have hy : y ∈ (genericSpecMap C F).fromNormalization ⁻¹ᵁ U := hxU
  letI iA := TopCat.Presheaf.algebra_section_stalk (genericSpecMap C F).normalization.presheaf
    (⟨y, hy⟩ : (genericSpecMap C F).fromNormalization ⁻¹ᵁ U)
  haveI := hV.isLocalization_stalk ⟨y, hy⟩
  let e := E.commRingCatIsoToRingEquiv
  letI : Algebra (integralClosure Γ(C, U) F) ((genericSpecMap C F).normalization.presheaf.stalk y) :=
    ((algebraMap _ _).comp e.symm.toRingHom).toAlgebra
  haveI := IsLocalization.isLocalization_of_base_ringEquiv
    (hV.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl
    ((genericSpecMap C F).normalization.presheaf.stalk y) e
  refine isIntegrallyClosed_of_isLocalization (R := integralClosure Γ(C, U) F) _
    (Submonoid.map e (hV.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl)
    (le_nonZeroDivisors_of_noZeroDivisors ?_)
  rintro ⟨x, hx, hx0⟩
  rw [map_eq_zero_iff e e.injective] at hx0
  subst hx0
  exact hx (Ideal.zero_mem _)

private theorem dimOne {Ω : Type} [Field Ω] {C : Scheme.{0}} [IsIntegral C] (c : C ⟶ Sp Ω)
    (hc : IsCurve c) (F : Type) [Field F]
    [Algebra C.functionField F] [FiniteDimensional C.functionField F]
    [QuasiCompact (genericSpecMap C F)] [QuasiSeparated (genericSpecMap C F)]
    [IsFinite (genericSpecMap C F).fromNormalization] :
    topologicalKrullDim (genericSpecMap C F).normalization = 1 := by
  obtain ⟨p0⟩ : Nonempty (Spec (CommRingCat.of F)) := inferInstance
  have hemb := GlobalTheory.topologicalKrullDim_eq_of_isEmbedding
    (e := (id : (genericSpecMap C F).normalization → (genericSpecMap C F).normalization))
    Topology.IsEmbedding.id (Z := Set.univ) Set.range_id
  rw [← hemb]
  refine GlobalTheory.topologicalKrullDim_eq_of_forall_exists_isOpen (Z := Set.univ)
    ⟨(genericSpecMap C F).toNormalization p0, trivial⟩ fun y _ => ?_
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset
    (x := (genericSpecMap C F).fromNormalization y) (U := ⊤) trivial
  haveI : Nonempty U := ⟨⟨_, hxU⟩⟩
  haveI : IsFractionRing Γ(C, U) C.functionField :=
    functionField_isFractionRing_of_isAffineOpen C U hU
  letI : Algebra Γ(C, U) F :=
    ((algebraMap C.functionField F).comp (algebraMap Γ(C, U) C.functionField)).toAlgebra
  haveI : IsScalarTower Γ(C, U) C.functionField F := IsScalarTower.of_algebraMap_eq' rfl
  obtain ⟨E, -⟩ := objIso F U hU
  have hV : IsAffineOpen ((genericSpecMap C F).fromNormalization ⁻¹ᵁ U) :=
    hU.preimage (genericSpecMap C F).fromNormalization
  refine ⟨((genericSpecMap C F).fromNormalization ⁻¹ᵁ U : Set _),
    ((genericSpecMap C F).fromNormalization ⁻¹ᵁ U).isOpen, hxU, ?_⟩
  have hinj : Function.Injective (algebraMap Γ(C, U) F) :=
    (algebraMap C.functionField F).injective.comp (IsFractionRing.injective Γ(C, U) C.functionField)
  haveI : FaithfulSMul Γ(C, U) (integralClosure Γ(C, U) F) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr fun a b h => hinj (congrArg Subtype.val h)
  rw [GlobalTheory.topologicalKrullDim_eq_of_isEmbedding hV.fromSpec.isOpenEmbedding.isEmbedding
    (by rw [hV.range_fromSpec, Set.inter_univ])]
  refine (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim
    Γ((genericSpecMap C F).normalization, (genericSpecMap C F).fromNormalization ⁻¹ᵁ U)).trans ?_
  rw [ringKrullDim_eq_of_ringEquiv E.commRingCatIsoToRingEquiv,
    GlobalTheory.ringKrullDim_eq_of_isIntegral Γ(C, U) (integralClosure Γ(C, U) F),
    CurveCut.CoverPf.krullDim_eq_one c hc U hU ⟨_, hxU⟩]
  rfl

private theorem surjNorm {C : Scheme.{0}} [IsIntegral C] (F : Type) [Field F]
    [Algebra C.functionField F] [QuasiCompact (genericSpecMap C F)]
    [QuasiSeparated (genericSpecMap C F)] : Surjective (genericSpecMap C F).fromNormalization := by
  constructor
  have hcl : IsClosedMap (genericSpecMap C F).fromNormalization :=
    (genericSpecMap C F).fromNormalization.isClosedMap
  have hη : genericPoint C ∈ Set.range (genericSpecMap C F).fromNormalization := by
    have h := GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model.genericSpecMap_closedPoint C F
    rw [← Scheme.Hom.toNormalization_fromNormalization (genericSpecMap C F)] at h
    exact ⟨_, h⟩
  have hsub : closure ({genericPoint C} : Set C) ⊆ Set.range (genericSpecMap C F).fromNormalization :=
    closure_minimal (Set.singleton_subset_iff.mpr hη) hcl.isClosed_range
  intro x
  exact hsub (specializes_iff_mem_closure.mp (genericPoint_specializes x))

private theorem restrictSquare {X Y : Scheme.{0}} (f : X ⟶ Y) [IsAffineHom f] {U : Y.Opens}
    (hU : IsAffineOpen U) :
    (f ∣_ U) ≫ hU.isoSpec.hom = (hU.preimage f).isoSpec.hom ≫ Spec.map (f.app U) := by
  rw [← cancel_mono hU.fromSpec, Category.assoc, IsAffineOpen.isoSpec_hom_fromSpec,
    morphismRestrict_ι, Category.assoc, Scheme.Hom.app_eq_appLE,
    IsAffineOpen.SpecMap_appLE_fromSpec f hU (hU.preimage f) le_rfl,
    ← Category.assoc, IsAffineOpen.isoSpec_hom_fromSpec]

theorem UpperTheory.exists_finite_surjective_curve_cover_of_functionField_extension :
    ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] {C : Scheme.{0}} (c : C ⟶ Sp Ω), IsCurve c →
        ∀ (hI : IsIntegral C) (F : Type) [Field F] [Algebra C.functionField F] [FiniteDimensional C.functionField F],
        ∃ (C' : Scheme.{0}) (γ : C' ⟶ C), IsCurve (γ ≫ c) ∧ Surjective γ ∧ IsFinite γ ∧
          ∀ (U : C.Opens) (hU : IsAffineOpen U) (_ : Nonempty U) (_ : Algebra Γ(C, U) F) (_ : IsScalarTower Γ(C, U) C.functionField F),
          ∃ e : (γ ⁻¹ᵁ U).toScheme ≅ Sp (integralClosure Γ(C, U) F),
            (γ ∣_ U) ≫ hU.isoSpec.hom = e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap Γ(C, U) (integralClosure Γ(C, U) F))) := by
  intro Ω _ _ C c hc hI F _ _ _
  haveI : IsProper c := hc.2.1
  haveI : QuasiSeparatedSpace C := quasiSeparatedSpace_of_quasiSeparated c
  haveI : IsFinite (genericSpecMap C F).fromNormalization := isFin c F
  refine ⟨(genericSpecMap C F).normalization, (genericSpecMap C F).fromNormalization,
    ⟨inferInstance, inferInstance, ?_⟩, surjNorm F, inferInstance, ?_⟩
  · exact UpperTheory.smooth_of_normal_curve_perfectField Ω ((genericSpecMap C F).fromNormalization ≫ c) inferInstance inferInstance
      (stalkClosed F) (dimOne c hc F)
  · intro U hU hne alg tower
    haveI := hne
    letI := alg
    haveI := tower
    obtain ⟨E, hE⟩ := objIso F U hU
    have hV : IsAffineOpen ((genericSpecMap C F).fromNormalization ⁻¹ᵁ U) :=
      hU.preimage (genericSpecMap C F).fromNormalization
    refine ⟨hV.isoSpec ≪≫ Scheme.Spec.mapIso E.symm.op, ?_⟩
    rw [restrictSquare _ hU, Iso.trans_hom, Category.assoc]
    congr 1
    have h2 : (genericSpecMap C F).fromNormalization.app U =
        CommRingCat.ofHom (algebraMap Γ(C, U) (integralClosure Γ(C, U) F)) ≫ E.inv := by
      rw [← hE, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rw [h2, Spec.map_comp]
    rfl
