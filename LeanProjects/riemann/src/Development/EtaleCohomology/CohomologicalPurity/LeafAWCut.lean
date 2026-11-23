import Development.EtaleCohomology.CohomologicalPurity.LeafIndExc
import Development.EtaleCohomology.KummerTheory.CupAWCut
import Development.EtaleCohomology.EtaleSheaves.LeafTwPairExistsPfExt
import Development.EtaleCohomology.EtaleSheaves.LeafTwTensExPf
import Development.EtaleCohomology.EtaleSheaves.LeafTwTensResPf
import Development.EtaleCohomology.TateTwists.EtaleTwistedResolutionExistsOfFlatSections
import Development.EtaleCohomology.TateTwists.EtaleTensorProductSheafExistsOfComponents
import Development.EtaleCohomology.TateTwists.EtaleTensorComplexUniversalOfDegreewise
import Development.EtaleCohomology.TateTwists.EtaleRootsOfUnityTwistFlatOfLocalFree
import Development.EtaleCohomology.TateTwists.EtaleCupProductFlipExistsOfComponents
import Development.EtaleCohomology.TateTwists.TtResSidePf
import Development.EtaleCohomology.TateTwists.TtTwistSidePf
import Development.EtaleCohomology.TateTwists.conePf
import Development.EtaleCohomology.TateTwists.acycIffPf
import Development.EtaleCohomology.TateTwists.ColumnOf
import Development.EtaleCohomology.TateTwists.EtaleTensorCycleLocallyLowersTopDegreeOfRowExact
import Development.EtaleCohomology.TateTwists.EtaleShortComplexExactIffLocallySurjectiveOnKernel
import Development.EtaleCohomology.TateTwists.EtaleTateTwistMultiplicationTensorExistsOfComple
import Development.EtaleCohomology.TateTwists.EtaleTateTwistLocalGenerationAndRootCompatOfPart
import Development.EtaleCohomology.TateTwists.EtaleTateTwistMultiplicationGeneratorMapOfSectio
import Development.EtaleCohomology.TateTwists.EtaleSheafMonoEpiIffSectionsOfSeparation
import Development.EtaleCohomology.TateTwists.EtaleTateTwistGeneratorMapInjectiveOfSectionsGlu
import Development.EtaleCohomology.TateTwists.EtaleTorsionCohomologyLocalizationBasic
import Development.EtaleCohomology.TateTwists.EtaleSectionsGlueOverCoverOfComponents

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC LateralTheory.EtaleFoundations

namespace LateralTheory.CohomologicalPurity.LeafAWCut

def LeafTwSec : Prop := EtaleTateTwistSectionsLocallyGenerated

theorem of_pair (h : LateralTheory.E.CupProductRingLaws.LeafTwPairExists) : LateralTheory.CohomologicalPurity.LeafAW := by
  intro q _ i j
  exact ⟨pick_spec (h q i j), fun E n m α β => LateralTheory.KummerTheory.CupAW_of (ZMod q) (twPair q i j) E rfl α β⟩

theorem row : EtaleTensorWithFlatPreservesLocalExactness := by
  intro R _ C J hJ hC s t V x hx
  have hA : C.Acyclic := fun n => (etale_short_complex_exact_iff_locally_surjective_on_kernel R (C.sc n)).2 (hC n)
  exact acyc.column_of R C J hJ ((acyc.acycIff_of R C).1 hA) V s t x hx

theorem tensAcyc : EtaleTensorAcyclicOfFlatBounded :=
  etale_tensor_complex_acyclic_of_locally_exact_flat etale_short_complex_exact_iff_locally_surjective_on_kernel (etale_tensor_complex_locally_exact_of_lifted_sections
    (etale_tensor_cycles_locally_lift_of_row_exact_and_descent row etale_tensor_cycle_locally_lowers_top_degree_of_row_exact))

theorem tensQis : EtaleTensorPairQuasiIsoOfFlatQuasiIso := etale_tensor_preserves_quasiIso_of_acyclic_and_cone tensAcyc tqis.cone_of

theorem pair_of (hq : EtaleTensorPairQuasiIsoOfFlatQuasiIso) (hm : EtaleTateTwistSingletonTensorGenMul) : LateralTheory.E.CupProductRingLaws.LeafTwPairExists :=
  LateralTheory.E.LeafTwPairExistsPf.LeafTwPairExists_of' LateralTheory.E.LeafTwTensExPf.LeafTwTensEx_of
    (LateralTheory.E.LeafTwTensResPf.leafTwTensRes_of
      (etale_tensor_twisted_resolution_of_existence_bound_and_sides LateralTheory.Fin.EtaleComplexTensorPairingExists.intersectionNumber_baseChange
        (fun R _ _ _ _ μ hI hJ hμ => (LateralTheory.Fin.EtaleTensorPairUniversalProperty.intersectionNumber_baseChange R μ hμ).2.1 hI hJ)
        (tt_twist_side_of hm LateralTheory.Fin.EtaleTateTwistSheafFlat.intersectionNumber_baseChange LateralTheory.Fin.EtaleComplexPairingFlipExists.intersectionNumber_baseChange hq)
        (tt_res_side_of LateralTheory.Fin.EtaleTensorPairUniversalProperty.intersectionNumber_baseChange hq))
      (fun q _ j t => (LateralTheory.Fin.EtaleTwistResolutionUniversalExtension.intersectionNumber_baseChange q j).2.1 t))

theorem twMul (hT : LeafTwSec) : EtaleTateTwistSingletonTensorGenMul :=
  etale_tate_twist_tensor_iso_of_generator_map_iso (etale_tate_twist_multiplication_tensor_exists_of_complex_tensor_exists LateralTheory.Fin.EtaleComplexTensorPairingExists.intersectionNumber_baseChange) (etale_tate_twist_multiplication_generator_map_of_section_description hT)
    (etale_tate_twist_generator_map_isIso_of_inj_surj etale_sheaf_mono_epi_iff_sections_of_separation
      (etale_tate_twist_generator_map_surjective_of_local_and_root (fun q _ i => (hT q i).1)
        (fun q _ j => ⟨(hT q j).2.2.2.1, fun U ζ ξ => (hT q j).2.1 U ζ (twGen j ξ)⟩))
      (etale_tate_twist_generator_map_injective_of_sections_glue hT LateralTheory.Fin.EtaleLocalPropertyBasicClosure.intersectionNumber_baseChange LateralTheory.Fin.EtaleSheafSectionsSeparatedAndGlue.intersectionNumber_baseChange))

theorem goal_of (h2 : LeafTwSec) : LateralTheory.CohomologicalPurity.LeafAW :=
  of_pair (pair_of tensQis (twMul h2))

end LateralTheory.CohomologicalPurity.LeafAWCut
