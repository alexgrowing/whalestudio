import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.MoriwakiBigness.HilbertSamuelApplications.DeepStROfUse
import Development.WeilBound.CoreStatements.HodgeTatePoints.AhSlim

namespace PositivityTheory.HtPt.Ah

open GlobalTheory.CompanionTheory.Ar

theorem deep_slim_use (h₁ : GlobalTheory.CompanionTheory.Hypotheses₂.ResolutionCharZero) (h₂ : GlobalTheory.CompanionTheory.Hypotheses₂.PrincipalisationCharZero)
    (hPL : GlobalTheory.CompanionTheory.Hypotheses₂.PoincareLelongInv) (hU : PositivityTheory.MbHsUse.HSUse)
    (hBig : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.MoriwakiBigStatement) (hF : HT.FarguesExact) (hZ : GR.ZarhinStatement)
    (hN : Pub.NefRR) : Plug.DeepStR :=
  Plug.deepStR_of_use (ais h₁ h₂ hPL) hU hBig (resK h₁ h₂) GlobalTheory.CompanionTheory.SAH.semiAbelianHomExtension
    (GlobalTheory.CompanionTheory.Relay.hodge_tate_of_fargues_exact hF) GlobalTheory.CompanionTheory.Gaga.gagaSections quot hZ hN

end PositivityTheory.HtPt.Ah
