import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoThreeFamily
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GeometricWeakTiesOfStrong
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RhoMemOfMkEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumRangeEqRoots
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MainTheoremPublishedInputsThirdStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EntryPointGAtParametersStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WeilUnitaryEntriesStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.BkLawEntriesStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LinkedBundlesGoodOfLocalLanglandsStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EntriesCombinedRealStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HarishChandraInputsCombinedStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.GoodFtEntriesStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RealGroupInputsCombinedStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EntryHPAAtParametersStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NonemptyExtensionEntriesStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GeometricZeroConditionAllStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.HypothesisBundleConversions

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc

namespace GlobalTheory.Fc.S0.Open0ProofU

theorem open_of_hypothesesUE : S0.HypothesesUE → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (cDep : ℝ), S0.Open0 (prm1 hL cDep) := by
  intro P hL cDep
  have hNE : ∀ K B f T w Z Wt p0 t nch n xd c, GlobalTheory.HeightCounting.Up.NEl hL cDep K B f T w Z Wt p0 t nch n xd c →
      Nonempty (GlobalTheory.HeightCounting.Up.NEb hL K B f T w Z Wt p0 t nch n xd c) := fun _ _ _ _ _ _ _ _ _ _ _ _ _ x => ⟨x.1⟩
  have hB : ∀ (K : Ctx) (q : WPt (prm1 hL cDep).s K), GlobalTheory.Mem.R3.Rw.BkLaw (q.w.D q.Z) := fun _ q => q.x.nx.2.1.2.down
  have hPA := GlobalTheory.T.entry_hPA_at_parameters hL (GlobalTheory.HeightCounting.Up.NEl hL cDep) SExt.none (geoCl anyGeometry)
  have hDc := GlobalTheory.T.entry_point_g_at_parameters hL (GlobalTheory.HeightCounting.Up.NEl hL cDep) SExt.none (geoCl anyGeometry)
  have hTie := GlobalTheory.T.nonempty_extension_entries P.discreteSeriesCover P.harishChandraModules P.casselmanWallach P.weilRepresentationUnitaryPair
    P.discreteSeriesExists P.harishChandraFinite P.cuspRapidDecay hL _ SExt.none (geoCl anyGeometry) hNE
  have hJ := GlobalTheory.T.entries_combined_real P.weilRepresentationUnitaryPair P.discreteSeriesExists P.discreteSeriesCover P.harishChandraModules
    P.casselmanWallach P.harishChandraFinite P.cuspRapidDecay hL _ SExt.none (geoCl anyGeometry) hPA hDc hTie
  have hMi := GlobalTheory.T.main_theorem_published_inputs_third P.harishChandraFinite P.cuspRapidDecay P.discreteSeriesCover P.harishChandraModules P.casselmanWallach
    GlobalTheory.Hk3.howeUnram_holds P.weilRepresentationUnitaryPair P.weilSiegelFormulaUnitary P.siegelWeilUnitaryConvergent
    P.doublingMethod P.unramifiedDoublingGL P.discreteSeriesClassification P.strongApproxSU P.siegelWeilUnitaryConvergent2
    hL (GlobalTheory.HeightCounting.Up.NEl hL cDep) SExt.none (geoCl anyGeometry)
  have hDiv := GlobalTheory.T.bk_law_entries P.weilRepresentationUnitaryPair P.discreteSeriesExists P.harishChandraFinite P.cuspRapidDecay
    P.discreteSeriesCover P.harishChandraModules P.casselmanWallach hL _ SExt.none (geoCl anyGeometry) hB hMi.1
  have hLam := GlobalTheory.T.real_group_inputs_combined P.weilRepresentationUnitaryPair P.discreteSeriesExists P.harishChandraFinite P.cuspRapidDecay
    P.harishChandraAnalyticity P.discreteSeriesClassification P.cuspTraceClass P.dixmierMalliavinFactorisation
    P.flathFactorisation P.pseudoCoefficientUpq P.harishChandraCharacters P.langlandsClassification P.labesseWaldspurger
    P.zelevinskyPolynomialRing P.geometricLemma P.greenCuspidal hL (GlobalTheory.HeightCounting.Up.NEl hL cDep) SExt.none (geoCl anyGeometry)
  have hKap := GlobalTheory.T.harish_chandra_inputs_combined P.harishChandraFinite P.cuspRapidDecay P.discreteSeriesCover P.harishChandraModules
    P.casselmanWallach P.harishChandraAnalyticity P.discreteSeriesClassification P.cuspTraceClass
    P.dixmierMalliavinFactorisation P.flathFactorisation P.pseudoCoefficientUpq P.harishChandraCharacters
    P.langlandsClassification P.labesseWaldspurger P.zelevinskyPolynomialRing P.geometricLemma P.greenCuspidal
    hL _ SExt.none (geoCl anyGeometry) hLam
  have hGood := GlobalTheory.T.linked_bundles_good_of_local_langlands (GlobalTheory.GreenBridge.green_of_regular P.greenRegularCharacters) P.zelevinskyPolynomialRing
    P.depthZeroInertia hL (GlobalTheory.HeightCounting.Up.NEl hL cDep) SExt.none (geoCl anyGeometry) hNE
  have hLab := GlobalTheory.T.good_ft_entries (GlobalTheory.GreenBridge.green_of_regular P.greenRegularCharacters) P.zelevinskyPolynomialRing
    P.depthZeroInertia hL _ SExt.none (geoCl anyGeometry) hNE hGood.1
  have hGeo := GlobalTheory.T.geometric_zero_condition_all P.rayClassFieldSt hL (GlobalTheory.HeightCounting.Up.NEl hL cDep) SExt.none (geoCl anyGeometry) hNE hDiv hTie
  have hDf := GlobalTheory.T.weil_unitary_entries P.weilRepresentationUnitaryPair P.discreteSeriesExists P.harishChandraFinite P.cuspRapidDecay
    hL (GlobalTheory.HeightCounting.Up.NEl hL cDep) SExt.none (geoCl anyGeometry)
  exact ⟨hPA, hLam, hDiv, hDc, hJ, hTie, hLab, hGood.2, hGeo, hMi.2, hKap, hDf⟩

end GlobalTheory.Fc.S0.Open0ProofU
