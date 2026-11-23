import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.DifferentiableOnDoublingIterate
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.EventuallyEqZeroOfIsBigOCubeOfDoubling
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.CubeSectionFacesAndDoubling
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.SeriesApplyEqZeroOfFace
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsLocalFrameCompatibleCube
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsGlobalFrameOfLocal
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.AutomorphyFactorExpLinearOfCube
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.AppellHumbertNormalFormOfLinearExponent
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ReFormPosOfThetaNeZero
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.BilinFormBijectiveOfNondegenerateMod
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.FourierCoeffUnitCubeTranslateOfEntirePeriodic
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.EntirePeriodicEqZeroOfFourierCoeffEqZero
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.CardLePowOfLinearIndependent
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.IsUnitOfLagrangian
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.CardLePowOfLinearIndependentThetaPrincipal
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsUniquePointOfRingHom
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.EqZeroOfForallAlgHomComplex
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.IsReducedSchemeOfSmoothOfIsIntegrallyClosed
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.HolFamilyOfIsPullback
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.IsTopologicalGroupComplexPoints
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.CompactSpacePointsPolAV
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsTestFunctionsSubsetOfMemNhds
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsEtaleCoordsVanishing
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ContinuousOnValue
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TangentBijectionOfValues
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsLinearLift
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.CubeTrivialisationOnUniformisingSpace
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsAppellHumbertFrameIsRig
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsConstOfCover
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.WeilIsExpRiemannForm
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.RiemannFormBijectiveOfWeilNondeg
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.SectionsPowThetaFunctions
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsIndepSections
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.IsAHOfPolarisation
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.MemSpanOfCardLe
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ThetaUnifAVOfParts

open AlgebraicGeometry CategoryTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem thetaUnifAV_of_laws :
    Out.CubeSt → Out.MulNSt → Out.WeilSt → Out.WeilNondegSt → Out.GlobalSectionsRankAlgClosed → ThetaUnifAV := by
  intro hcube hmul hpair hnd hsec
  have hval := @valAt'_rules
  have hvalaff := @existsUnique_point_of_ringHom
  have hvalext := @eq_of_valAt'_eq hval hvalaff
  have hsmred := @isReduced_of_smooth_complex
  have hchring := @exists_holomorphic_section_of_etale
  have hchart := @HolChart.exists_holomorphic_chart hval hvalaff hchring
  have hcpt := @PointsCompact.compactSpace_points_polAV hval hvalaff
  have hholprod := @holFamily_lift hval
  have htopgrp := @isTopologicalGroup_complexPoints hval
  have hexp := @AbelianExp.exists_holUnif hmul hval hholprod htopgrp hcpt hchart
  have htan := @TangentOrigin.tangent_bijection_of_values hval
  have hendo := @EndoLinear.exists_linear_lift hval
  have hcubet := @cube_trivialisation_on_uniformising_space hval hholprod
  have hdbl := @exists_doubling_solution_pi
  have hdblu := @eventually_eq_zero_of_isBigO_cube_of_doubling
  have hlock := @LocalCube.exists_third_difference hdbl hdblu
  have hface := @cube_section_faces_and_doubling
  have hlocframe := @exists_localFrame_compatible_cube @hface hlock
  have hglobframe := @CubeFrame.exists_global_frame
  have hautfactor := @automorphyFactor_exp_linear_of_cube
  have hahform := @appellHumbert_normal_form_of_linear_exponent
  have hframe := @exists_appellHumbert_frame_isRig hcube hval hcubet
    @hlocframe @hglobframe @hautfactor hahform
  have hthg := @ThetaGroupFrame.thetaGrp_in_frame hval hholprod
  have hweil := @WeilExp.weilIs_exp_riemannForm hpair hval hvalext hsmred hthg
  have hunimod := @bilinForm_bijective_of_nondegenerate_mod
  have hperf := @riemannForm_bijective_of_weilNondeg hnd hunimod hweil
  have hsecfn := @sections_pow_theta_functions hval hvalext hsmred
  have hfshift := @fourierCoeff_unitCube_translate_of_entire_periodic
  have hfvan := @entire_periodic_eq_zero_of_fourierCoeff_eq_zero hfshift
  have hdimcl := @ClassicalTheta.card_le_pow_of_linearIndependent hfshift hfvan
  have hnormform := @SiegelNormalForm.exists_normal_form
  have hdim := @card_le_pow_of_linearIndependent_theta_principal hnormform hdimcl
  have hindep := @PowSec.exists_indep_sections hsec
  have hpos := @ThetaPositivity.re_form_pos_of_theta_ne_zero
  have hisah := @isAH_of_polarisation hval hpos hindep hsecfn
  have hseconto := @ThetaOnto.theta_from_section hval hdim hindep hsecfn
  exact thetaUnifAV_of_parts hexp htan hendo hframe hweil hperf hsecfn hseconto hisah

end GlobalTheory
