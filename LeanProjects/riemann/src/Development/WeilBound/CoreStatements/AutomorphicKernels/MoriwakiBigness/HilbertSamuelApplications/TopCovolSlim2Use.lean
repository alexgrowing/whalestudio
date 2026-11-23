import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.MoriwakiBigness.HilbertSamuelApplications.AhSlimU
import Development.WeilBound.CoreStatements.NefModelVolumes.TopCovolSlim2
open NumberField Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Indef.Tree Formalism.IndefR.Obj
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [-instance] GlobalTheory.CompHt.fintypePsi

namespace SelfIntersectionVolumeEstimates

set_option maxHeartbeats 1000000 in

theorem topCovolSlim2_use : GlobalTheory.CompanionTheory.Hypotheses₂.ResolutionCharZero → GlobalTheory.CompanionTheory.Hypotheses₂.PrincipalisationCharZero → GlobalTheory.CompanionTheory.Hypotheses₂.PoincareLelongInv → PositivityTheory.MbHsUse.HSUse → ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.MoriwakiBigStatement → HT.FarguesExact → GR.ZarhinStatement → Pub.NefRR → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS → GlobalTheory.Published.SemiAbelianLieSeminegative → GlobalTheory.Published.PointSeparationPair → GlobalTheory.Published.ArDegree → GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.Published.ScholzeWeinsteinB → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.CovTop.CovolX :=
  fun h₁ h₂ hPL hU hBig hFar hZar hRR hS hK hN hSep hDeg hP hSW hGD =>
    have hX : GlobalTheory.CovTop.HypothesesX := ⟨hK, hN, GlobalTheory.GreenBridge.green_of_regular GlobalTheory.greenRegularCharacters_holds, hSep, FubiniStudyChowHeightFormula₂.fubiniStudyChowHeight_of_hypotheses hP⟩
    have hF := PositivityTheory.Prw.toroidalChartsForFan_of hK
    have hH : GlobalTheory.CovHt.HypothesesH := ⟨hS, hF, GlobalTheory.Published.toroidalCharts_of_siegel_of_forFan hS hF, hDeg⟩
    topCovolG ⟨ChowFormHeightComparison₂.hermitian_sections_height_bound, PositivityTheory.Xj7N.injectivity_weight_sections (GlobalTheory.CompanionTheory.Ar.Rec.exists_nonvanishing_of_toroidal hH.sieg hX.ks)⟩ hX hP hH hSW hGD ⟨hP.q6, hP.q8, hP.q13, hP.q7, hP.q10, GlobalTheory.Published.chowFormIntExists_holds, ChowFormCompatibility.chow_form_hyperplane_section, hP.q12⟩
      (PositivityTheory.HtPt.Ah.deep_slim_use h₁ h₂ hPL hU hBig hFar hZar hRR)

end SelfIntersectionVolumeEstimates
