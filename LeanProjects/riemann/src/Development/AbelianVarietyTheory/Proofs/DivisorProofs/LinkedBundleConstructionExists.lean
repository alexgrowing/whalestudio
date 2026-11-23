import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DepthZeroSupport
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoThreeFamily
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GeometricWeakTiesOfStrong
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GKeyFin
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnlocalizedSaturatedState
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ArchimedeanInputsImplyStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DoublingInputsImplyStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeightSetSaturatedOfHypsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalRepresentationInputsImplyStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemberBuiltLinkedGeometricStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemberPreservedLargeGridStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BuiltLinkedLargeGridStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SlotStageMovesGeometricStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.HypothesisBundleConversions
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalLanglandsHypothesesOfLiteratureStatement

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Mem.LiteralAutomorphy

namespace GlobalTheory.Fc.StageOneU

set_option maxHeartbeats 1000000 in

theorem member_bundles_large_ue : S0.HypothesesUE → S0.RowRat →
    ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (cDep : ℝ) (A : GroupRetwisting.AtP), EvLgG A →
      StandardLattice.SiegelMassRatioCM ∧
      MemberE (prmR (NEa hL (GlobalTheory.HeightCounting.Up.NEo hL cDep) A) SExt.none (geoCl anyGeometry)).s ∧
      ExBL KPx (IsBuiltE (prmR (NEa hL (GlobalTheory.HeightCounting.Up.NEo hL cDep) A) SExt.none (geoCl anyGeometry)).s)
        (IsGoodE (prmR (NEa hL (GlobalTheory.HeightCounting.Up.NEo hL cDep) A) SExt.none (geoCl anyGeometry)).s)
        (IsLinked (prmR (NEa hL (GlobalTheory.HeightCounting.Up.NEo hL cDep) A) SExt.none (geoCl anyGeometry))) := by
  intro P hR hL cDep A hEv
  have sw := P.siegelWeilUnitaryConvergent2
  have hA := GlobalTheory.T.archimedean_inputs_imply P.globalArtinReciprocity P.cMCurveGoodOutsidePrimeSt P.weberRayFieldSt
    P.harishChandraModules P.cuspRapidDecay P.casselmanWallach P.harishChandraFinite
    P.discreteSeriesClassification P.discreteSeriesCoverExists P.besselUniquenessReal
    P.formalDegreeCompactDual sw
  have hPM : PrM := ⟨P.harishChandraAnalyticity, P.discreteSeriesClassification, P.cuspRapidDecay,
    P.harishChandraFinite, P.cuspTraceClass, P.dixmierMalliavinFactorisation, P.flathFactorisation,
    P.pseudoCoefficientUpq, P.harishChandraCharacters, P.langlandsClassification,
    P.labesseWaldspurger, P.zelevinskyPolynomialRing, P.geometricLemma, P.greenCuspidal⟩
  have hH := GlobalTheory.T.doubling_inputs_imply hPM P.harishChandraModules P.discreteSeriesCover P.casselmanWallach
    P.weilSiegelFormulaUnitary P.siegelWeilUnitarySchrodinger P.siegelEisensteinContinuation
    P.siegelEisensteinSimplePole P.unramifiedDoublingGL P.bernsteinZelevinskyFiniteness
    P.schurOrthogonalitySquareIntegrable P.regularisedSiegelWeilFirstTerm hR
  have hW := GlobalTheory.T.exists_unlocalized_saturated_state_of_hypA_hypH hA hH
  have hM := GlobalTheory.T.local_representation_inputs_imply P.harishChandraAnalyticity P.discreteSeriesClassification
    P.cuspRapidDecay P.harishChandraFinite P.cuspTraceClass P.dixmierMalliavinFactorisation
    P.flathFactorisation P.pseudoCoefficientUpq P.harishChandraCharacters
    P.langlandsClassification P.labesseWaldspurger P.zelevinskyPolynomialRing P.geometricLemma
    P.greenCuspidal hL (GlobalTheory.HeightCounting.Up.NEo hL cDep) SExt.none (geoCl anyGeometry)
  obtain ⟨hE, -, -, hL', hN⟩ := GlobalTheory.T.local_langlands_hypotheses_of_literature P.litN P.toHypothesesX
  exact ⟨hA.a18,
    GlobalTheory.T.member_preserved_large_grid hL _ _ _ A hEv (GlobalTheory.T.member_built_linked_geometric hA hE hH hW hL hN cDep hM).1,
    GlobalTheory.T.built_linked_large_grid hA hH hPM hL _ _ A (fun _ _ _ _ _ _ _ _ _ _ _ _ _ x => ⟨x.1.1⟩)
      (GlobalTheory.T.movable_geometric hL cDep anyGeometry)⟩

end GlobalTheory.Fc.StageOneU
