import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ForallGeometricallyIntegralOfSmoothOfGeometrical
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.UnramExtLaw
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SmoothDense
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueSecEqMulGen
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsGenOfMemChart
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsGenOfLocalOnBase
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.MulPullOfCubeOfSymm
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LocGenOfTrivial
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SymmetricLiftOddOrderExistsUnique
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueDescendOfTorsionInvariant
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.NatCardEqOfEquivPiField
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FinrankSectionsLineBundlePowEqPow
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.EqOneOfPowEqOneOfCongrOne
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsEqPowOfTorsionCompEqOne
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsHasProjectiveDimensionLEOfResidueField
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsPrincipalMapAwayOfHasProjectiveDimensionLE
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.UniqueFactorizationMonoidOfIsRegularRingOfIsLoca
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsRegularRingOfSmooth
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsLineBundleExtension
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsRegularRingOfIsDiscreteValuationRing
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.EqCompSectionOfSurjectiveAppTop
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ThetaGrpActsLinearly
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsIffCommIsOfAndLiftSubsingleton
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LinearIndependentOfCommSmul
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsFieldGlobalFnsSpec
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.TwistedPowTranslate
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SecMInvariantEqBotOrUnivAtGeometricPoint
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsSecValueIsUnit
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GoodPtOfIrredOfMulPull
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsGenOfAssociated
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsSectionsSpanAffine
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsUnitIffMem
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SpanEqTopOfFunctionals
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.EqIdOfFixesTorsion
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.MemRangeOfSumEqZero
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsOddNeZero
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CompAutEqOfSerreBaseChange
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsMulEqSmulOneOfMulVecInjective
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.VeryAmpleByOfRelAmple
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FirstCohomologyVanishesOfIsoOfIsGen
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FirstCohomologyVanishesDescent
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SecBaseChangeOfPerf
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FinrankOfIsSecBasis
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.NonemptyPerfectSectionsComplexOfSmoothProjStatement
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SerreVanishingVeryAmpleStatement
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsIdPowEqOneOfIsFiniteOfFlat
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsBasisMemOfSpanEqTopOfSemilocal
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FiniteFaithfullyFlatKer
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsQuotientSchemeOfFiniteFlatSubgroup
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.QuotientIsAbelianSchemeOfQuotientScheme
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsOfCubeBundleGenerator
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CubeTheoremAndSectionsFiniteGrowthAbelianVariety

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbLaw.AllLaws

theorem laws_of_h0_eq_one :
    (∀ (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Spec (CommRingCat.of K))), Module.finrank Γ((baseOver (Spec (CommRingCat.of K))).left, ⊤) (SecM P.A P.L 1 (baseOver (Spec (CommRingCat.of K)))) = 1) → Laws ∧ Laws2 := by
  intro h1
  have gi := GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected
  obtain ⟨g, rig, pbc, lemB, cext⟩ := GlobalTheory.laws_without_cohomology
  obtain ⟨cg, fin, grow⟩ := GlobalTheory.AbLaw.CubeAssembly.cube_and_sections
  obtain ⟨cube, square, mulPull, kerPow, weil, symLift, nondeg, charPair, mulq, rel⟩ :=
    GlobalTheory.AbLaw.FromCube.all_of_cubeGen cg
  have sq := (GlobalTheory.AbSquare.square_of_cube cg).1
  have neg := GlobalTheory.exists_gen_negLB g
  have mp := (GlobalTheory.MulPull.mulPull_of_cube_of_symm cg neg).1
  have ker := (GlobalTheory.kerPow_of_square sq).1
  have lft := (GlobalTheory.kerPow_of_square sq).2.2
  have sym := (GlobalTheory.symLift_odd g lft neg).1
  have wc := GlobalTheory.weilIs_iff_commIsOf_and_lift_subsingleton g lft sym
  have w₃ := GlobalTheory.weilIs_alternating_skew_natural g lft
  have act := GlobalTheory.thetaGrp_acts_linearly g
  have gal := GlobalTheory.torsion_invariant_descends mulq
  have tw := GlobalTheory.twisted_pow_translate sq mulq
  have proj := GlobalTheory.AbLaw.polAV_veryAmpleBy pbc
  have h0 : GlobalSectionsRankAlgClosed := GlobalTheory.FinrankGrowthBounds.finrank_sections_lineBundlePow_eq_pow gi h1 rel grow mulq
  have mulN : MulNSt := GlobalTheory.mulN_of_decomposition mulq rel h0 pbc
  have h0T := (GlobalTheory.secM_invariant_eq_bot_or_univ_at_geometric_point pbc).1 h0
  have van := GlobalTheory.AbLaw.PowVanish.first_cohomology_vanishes_powers proj GlobalTheory.T.serre_vanishing_very_ample.1 GlobalTheory.AbLaw.h1Zero_of_isIso mp mulq gal
  obtain ⟨sbcAny, sbc⟩ := GlobalTheory.AbLaw.SecBC.secBaseChange_of_perf GlobalTheory.T.nonempty_perfectSectionsComplex_of_smooth_proj proj van
    GlobalTheory.AbLaw.h1Zero_of_isIso GlobalTheory.exists_matrix_basis_ker_of_exact_at_point pbc h0T
  have stw : SecTwistSt := GlobalTheory.SecTwist.secTwist_of_perf GlobalTheory.T.nonempty_perfectSectionsComplex_of_smooth_proj proj van
    GlobalTheory.AbLaw.h1Zero_of_isIso GlobalTheory.exists_matrix_basis_ker_of_exact_at_point pbc h0T tw
  have irred : IrredSt :=
    GlobalTheory.irredSt_of_heis act wc GlobalTheory.heisenberg_family_irreducible weil w₃ nondeg mulN h0
  have irrT := (GlobalTheory.secM_invariant_eq_bot_or_univ_at_geometric_point pbc).2 irred
  have gen := GlobalTheory.NoBasePoint.exists_sec_value_isUnit gi sq h0T mulq
  have mono := GlobalTheory.SepPoints.eq_of_forall_value_eq gi cg sbc mulq
  have ample : AmpleSt :=
    GlobalTheory.VeryAmplePow.ample (GlobalTheory.exists_sections_span_affine sbc) gen mono
  have goodPt : GoodPtSt := GlobalTheory.GoodPoint.goodPt_of_irred gi irred act ker mp mulq gen
  have vv := GlobalTheory.VVRank.vvRank sbcAny irrT mp lft act ker pbc mulq
  have finOrd := GlobalTheory.TorsionFixedAut.eq_id_of_fixes_torsion g symLift act wc irred h0 ample kerPow
  have sep := GlobalTheory.EndDivisible.eq_one_of_forall_pow_dvd gi mp fin
  have serreK := GlobalTheory.SerreField.serre_algClosed mulq
    (GlobalTheory.DivisibleHom.exists_eq_pow_of_torsion_comp_eq_one mulq) sep finOrd
    GlobalTheory.eq_one_of_pow_eq_one_of_congr_one
  have serre : SerreSt := GlobalTheory.serre_of_algClosed pbc g GlobalTheory.local_rigidity serreK
  have ext : Semi.extend_existsSt.{0} :=
    GlobalTheory.ExtendRig.extend_exists gi GlobalTheory.isRegularRing_of_smooth
      (GlobalTheory.uniqueFactorizationMonoid_of_isRegularRing_of_isLocalRing
        GlobalTheory.exists_hasProjectiveDimensionLE_of_isRegularLocalRing
        GlobalTheory.isPrincipal_map_away_of_hasProjectiveDimensionLE)
      GlobalTheory.exists_lineBundle_extension
  have quot : QuotientSt :=
    GlobalTheory.quotient_isAbelianScheme_of_quotientScheme gi
      (GlobalTheory.exists_quotient_scheme_of_finite_flat_subgroup GlobalTheory.FiniteFlatKilled.main
        (GlobalTheory.HopfQuot.affine_quotient GlobalTheory.exists_basis_mem_of_span_eq_top_of_semilocal) mulq)
  exact ⟨⟨h0, sbc, ample, kerPow, mulPull, mulN, cube, square, rig, weil, nondeg, symLift, irred,
    goodPt, serre, ext, cext, lemB, GlobalTheory.EvVal.evValSt, vv, g, pbc, quot, GlobalTheory.unramExt_law⟩,
    ⟨sbcAny, stw, charPair, GlobalTheory.smoothDense⟩⟩

end GlobalTheory.AbLaw.AllLaws
