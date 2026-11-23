import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ArithIntersectionSystemOfPoincareLelongStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.DeepStROfHyp
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ArithIntersectionSystemOfPoincareLelong
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HodgeTateOfFarguesExact
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.SemiAbelianHomExtension
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.QuotientByFiniteFlatOfFreeQuotient
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FreeQuotientSchemeHolds
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ResKOfResolutionPrincipalisation
import Development.AutomorphicSpectrum.Proofs.MetricProofs.PoincareLelongOfInv
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LineOfLargeDegreeOfMoriwaki
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.GagaSections

namespace PositivityTheory.HtPt.Ah

open GlobalTheory.CompanionTheory.Ar

theorem resK (h₁ : GlobalTheory.CompanionTheory.Hypotheses₂.ResolutionCharZero) (h₂ : GlobalTheory.CompanionTheory.Hypotheses₂.PrincipalisationCharZero) :
    ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement :=
  GlobalTheory.CompanionTheory.Hypotheses₂.ResKSide.resK_of_resolution_principalisation h₁ h₂

theorem ais (h₁ : GlobalTheory.CompanionTheory.Hypotheses₂.ResolutionCharZero) (h₂ : GlobalTheory.CompanionTheory.Hypotheses₂.PrincipalisationCharZero)
    (hPL : GlobalTheory.CompanionTheory.Hypotheses₂.PoincareLelongInv) : ReciprocityTheory.ChartRestriction.G.Geo.ArithIntersectionSystemStatement :=
  Pub.arithIntersectionSystem_of_poincareLelong_resK (Tw.Main.poincareLelong_of_inv (resK h₁ h₂) hPL) (resK h₁ h₂)

theorem quot : GR.QuotientByFiniteFlatStatement :=
  GR.QuotSide.quotientByFiniteFlat_of_freeQuotient GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuotientScheme_holds

theorem deep_slim (h₁ : GlobalTheory.CompanionTheory.Hypotheses₂.ResolutionCharZero) (h₂ : GlobalTheory.CompanionTheory.Hypotheses₂.PrincipalisationCharZero)
    (hPL : GlobalTheory.CompanionTheory.Hypotheses₂.PoincareLelongInv) (hHS : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.MoriwakiHSStatement)
    (hBig : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.MoriwakiBigStatement) (hF : HT.FarguesExact) (hZ : GR.ZarhinStatement)
    (hN : Pub.NefRR) : Plug.DeepStR :=
  Plug.deepStR_of_hodgeTate (ais h₁ h₂ hPL) hHS hBig (resK h₁ h₂) GlobalTheory.CompanionTheory.SAH.semiAbelianHomExtension
    (GlobalTheory.CompanionTheory.Relay.hodge_tate_of_fargues_exact hF) GlobalTheory.CompanionTheory.Gaga.gagaSections quot hZ hN

end PositivityTheory.HtPt.Ah
