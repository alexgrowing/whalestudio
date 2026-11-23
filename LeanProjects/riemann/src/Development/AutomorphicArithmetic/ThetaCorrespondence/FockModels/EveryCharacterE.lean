import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesCoefficientsCuspidalIffOneSided
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DepthZeroSupport
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoThreeFamily
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GeometricWeakTiesOfStrong
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GKeyFin
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnlocalizedSaturatedState
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DiscreteBranchingUpq
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LevelPlusSubgroup
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RhoMemOfMkEq
import Development.AbelianVarietyTheory.Definitions.Divisors.HypothesisBundleConversions
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalityOfThetaHypothesesStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowRatWOfRowTest
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Fun0FitOfJoin
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvLgGGridAOfJoin
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilConvergenceOfSiegelSet
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalMatchingOfHoweDualityStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaIntegralsOfMinguezStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LargeFieldLinkedBundlesExist
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.OpenImpliesL3AtLinkedBundles
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.OpenAndLinkedMonoExtension
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OntoXAndLamLowOfPublishedUE
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OpenFirstParametersOfPrintsUEStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyHypsOfPublishedUE
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumRangeEqRoots
import Development.AutomorphicArithmetic.CharacterBoxes.EveryCharacter
import Development.AutomorphicArithmetic.ResidueCharacters.ClosedOfAll
import Development.AutomorphicArithmetic.ThetaCorrespondence.FockModels.RealBranch
import Development.AutomorphicArithmetic.ThetaCorrespondence.FockModels.ArakSwapCovol
import Development.AutomorphicArithmetic.ThetaCorrespondence.PrismaticDieudonne.PrismaticDieudonneHodge
import Development.WeilBound.ThetaLifts.Reductions.FiniteClosure.TheoremKOfMod
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Mem.LiteralAutomorphy

namespace UpperTheory.Lit

open UpperTheory.Top

theorem hypsE₂ : S0.HypothesesUE → GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → GlobalTheory.CovTop.CovolX → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL), (∀ cDep : ℝ, RL.At (prm1 hL cDep) (fun Q L => R1.PredicateAtBundlePoints Q L fun 𝒞 => Formalism.MainNotions.Closed 𝒞 fun Fm _ => GlobalTheory.NLink.BoundAtTwoAndThreeForFamily Fm)) → Nonempty (Hyps S0.NL DRS) := by
  intro P F hA hM hX hL hN
  have C := P.litN
  have hS : GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.FunctionalsSeparate :=
    functionalsSeparate_free F GlobalTheory.Hk3.howeUnram_holds P.siegelWeilUnitaryConvergent
  have hRat : S0.RowRat := GlobalTheory.Mem.LiteralAutomorphy.rowRatW_of_rowTest (GlobalTheory.T.rationality_of_theta_hypotheses F.siegelSetUnitary F.howeDualityReal
    P.greenCuspidal F C.join C.fe hA hM hS)
  have hFit : GlobalTheory.BigTop.Fun.Fun0Fit @GlobalTheory.BigTop.Fun.Fld := GlobalTheory.BigTop.Fun.Close.fun0Fit_of_join F C.join C.fe hA hM hS (GlobalTheory.Fc.S0.ontoX_and_lamLow_of_classicalTheoremsUE P).2
  obtain ⟨CF1, hCF1⟩ := GlobalTheory.Mem.LiteralAutomorphy.evLgG_gridA_of_join F.howeDualityReal hM F C.join C.fe hA
    (GlobalTheory.WeilConv.weilConvergence F.siegelSetUnitary F) (GlobalTheory.T.local_matching_of_howe_duality F.howeDualityReal F hA hM)
    (GlobalTheory.T.theta_integrals_of_minguez F.minguezThetaGL F hA hM) hS
  obtain ⟨CF0, hCF0⟩ := GlobalTheory.Fc.StageOne.rowFun_at_gridA P.discreteSeriesCover P.harishChandraModules P.cuspRapidDecay P.casselmanWallach
    P.rayClassFieldSt hFit
  have hEv : EvLgG (GridA (max CF0 CF1)) := hCF1 _ (le_max_right _ _)
  have hOpen1 : S0.Open0 (prm1 hL (max CF0 CF1)) := GlobalTheory.T.open_first_parameters_of_hypothesesUE P hL (max CF0 CF1)
  have hMono := GlobalTheory.Glob.open_and_linked_of_stronger_extension hL (GlobalTheory.HeightCounting.Up.NEl hL (max CF0 CF1))
    (NEa hL (GlobalTheory.HeightCounting.Up.NEo hL (max CF0 CF1)) (GridA (max CF0 CF1))) SExt.none (geoCl anyGeometry)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ x => ⟨x.1.1⟩)
  have hOpenA := hMono.2 hOpen1
  have hFun := hCF0 (max CF0 CF1) (le_max_left _ _) hL (GlobalTheory.HeightCounting.Up.NEo hL (max CF0 CF1)) SExt.none (geoCl anyGeometry)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ x => ⟨x.1⟩) hOpenA
  have hL3 := GlobalTheory.Glob.CovolRow.linked_bundles_l3_of_open P.discreteSeriesCover P.harishChandraModules P.cuspRapidDecay
    P.casselmanWallach P.rayClassFieldSt hX hL (NEa hL (GlobalTheory.HeightCounting.Up.NEo hL (max CF0 CF1)) (GridA (max CF0 CF1)))
    SExt.none (geoCl anyGeometry) (fun _ _ _ _ _ _ _ _ _ _ _ _ _ x => ⟨x.1.1.1⟩) hOpenA
  exact GlobalTheory.Fc.S0.StageU.nonempty_hyps_of_classicalTheoremsUE P hRat hL (max CF0 CF1) (GridA (max CF0 CF1)) hEv (hN (max CF0 CF1)) hFun hL3

theorem everyE₂ (P : S0.HypothesesUE) (F : GlobalTheory.FunPr.Hypotheses₂) (hA : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree)
    (hM : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching) (hX : GlobalTheory.CovTop.CovolX) (hL : GlobalTheory.Published.LocalLanglandsGL) (hV : VWin) :
    UpperTheory.EveryCharacter :=
  plugAll (GlobalTheory.GreenBridge.green_of_regular P.greenRegularCharacters) hV
    (hypsE₂ P F hA hM hX hL fun cDep => UpperTheory.N.boundAtTwoThree_at_prm_of_prints P.nLink (prm1 hL cDep))

structure CovE : Prop where
  res : GlobalTheory.CompanionTheory.Hypotheses₂.ResolutionCharZero
  princ : GlobalTheory.CompanionTheory.Hypotheses₂.PrincipalisationCharZero
  pl : GlobalTheory.CompanionTheory.Hypotheses₂.PoincareLelongInv
  zar : GlobalTheory.CompanionTheory.Ar.GR.ZarhinStatement
  nef : GlobalTheory.CompanionTheory.Ar.Pub.NefRR
  sieg : GlobalTheory.Published.SiegelToroidalIntegral
  ks : GlobalTheory.Published.ToroidalForFanKS
  neg : GlobalTheory.Published.SemiAbelianLieSeminegative
  sep : GlobalTheory.Published.PointSeparationPair
  deg : GlobalTheory.Published.ArDegree
  two : GlobalTheory.CovTop.Hypotheses2
  sw : GlobalTheory.Published.ScholzeWeinsteinB
  gd : GlobalTheory.Published.GrothendieckDeformation

end UpperTheory.Lit
