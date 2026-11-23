import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DepthZeroSupport
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoThreeFamily
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GeometricWeakTiesOfStrong
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GKeyFin
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnlocalizedSaturatedState
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.OpenAndLinkedMonoExtension
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LinkedBundlesOfCasselmanWallach
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LinkOfClosedAtFamily
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NonemptyHypsOfAllRows
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LitThin
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.GenusMassAtTwo
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryHyperplaneVolumeRatioSiegelWeil
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowsPosTypeP
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowsFinDimLink
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.WuDecayOfGap
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowMainEqPOfSiegelWeil
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowPositivityOfSiegelWeil
import Development.AbelianVarietyTheory.Definitions.Divisors.HypothesisBundleConversions
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalLanglandsHypothesesOfLiteratureStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinkedBundleConstructionExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OntoXAndLamLowOfPublishedUE
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OpenFirstParametersOfPrintsUEStatement

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Mem.LiteralAutomorphy

namespace GlobalTheory.Fc.S0.StageU

theorem nonempty_hyps_of_classicalTheoremsUE : S0.HypothesesUE → S0.RowRat → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (cDep : ℝ) (A : GroupRetwisting.AtP), EvLgG A → RL.At (prm1 hL cDep) (fun Q L => R1.PredicateAtBundlePoints Q L fun 𝒞 => Formalism.MainNotions.Closed 𝒞 fun Fm _ => GlobalTheory.NLink.BoundAtTwoAndThreeForFamily Fm) → RL.At (prmR (NEa hL (GlobalTheory.HeightCounting.Up.NEo hL cDep) A) SExt.none (geoCl anyGeometry)) S0.FunctorialityCondition → RL.At (prmR (NEa hL (GlobalTheory.HeightCounting.Up.NEo hL cDep) A) SExt.none (geoCl anyGeometry)) S0.CovolumeBound' → Nonempty (Hyps S0.NL DRS) := by
  intro P hR hL cDep A hA hN hF hL3
  obtain ⟨hP, hMem, hEx⟩ := GlobalTheory.T.linked_bundle_construction_exists P hR hL cDep A hA
  obtain ⟨_, prN, serN, _⟩ := GlobalTheory.T.local_langlands_hypotheses_of_literature P.litN P.toHypothesesX
  have hOL := GlobalTheory.Fc.S0.ontoX_and_lamLow_of_classicalTheoremsUE P
  have hO := GlobalTheory.T.open_first_parameters_of_hypothesesUE P hL cDep
  have hNrow := GlobalTheory.NLink.Final.main P.nLink prN P.toHypothesesX serN P.depthZeroWild' P.depthZeroSupport'
    P.localFiniteness P.localTateDuality P.localEulerChar hL cDep hN
  have hmono := GlobalTheory.Glob.open_and_linked_of_stronger_extension hL (GlobalTheory.HeightCounting.Up.NEl hL cDep) (NEa hL (GlobalTheory.HeightCounting.Up.NEo hL cDep) A) SExt.none (geoCl anyGeometry)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ x => ⟨x.1.1⟩)
  have hO' := hmono.2 hO
  have hN' : RL.At (prmR (NEa hL (GlobalTheory.HeightCounting.Up.NEo hL cDep) A) SExt.none (geoCl anyGeometry)) (fun Q L => R1.PredicateAtBundlePoints Q L S0.NL) :=
    hmono.1 (fun 𝒜 _ => S0.NL (Cp.D3 3 𝒜)) hNrow
  have hAll := GlobalTheory.Fc.AllAtMemberStage0.allRows_of_open0 P.globalArtinReciprocity P.siegelWeilUnitaryConvergent2 P.discreteSeriesCover
    P.harishChandraModules P.cuspRapidDecay P.casselmanWallach P.discreteSeriesClassification hOL.1 hOL.2
    hL _ _ _ S0.NL hO' hL3 hF hN'
  exact GlobalTheory.Fc.nonempty_hyps_of_allRows hP GlobalTheory.ThinScaleLiterature.litThin GlobalTheory.wuDecayOfGap GlobalTheory.rowsFinDim_link
    GlobalTheory.rowsPos_typeP (GlobalTheory.rowNGP_of_siegelWeil P.siegelWeilUnitaryConvergent2)
    (GlobalTheory.rowMainEqP_of_siegelWeil P.siegelWeilUnitaryConvergent2)
    (GlobalTheory.VolRatioFromSiegelWeil.volumeRatio P.siegelWeilUnitaryConvergent2) GlobalTheory.genusMassAt_two
    KPx _ _ _ S0.NL DRS (fun _ => hMem) hEx hAll

end GlobalTheory.Fc.S0.StageU
