import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.MoriwakiBigness.HilbertSamuelApplications.GivenOfUse
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GoodTowerVolumeTheoremAlt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.Link

theorem good_tower_volume_theorem_bis :
    ReciprocityTheory.ChartRestriction.G.Geo.ArithIntersectionSystemStatement → PositivityTheory.MbHsUse.HSUse →
    ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.MoriwakiBigStatement → ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement →
    GlobalTheory.Published.SemiAbelianHomExtension → HT.FarguesHodgeTate → Flat.GagaSections →
    GroundTheory.Heights₂.Heights.LineOfLargeDegree.Statement → GR.QuotientByFiniteFlatStatement → GR.ZarhinStatement →
    Top.GoodTowerExistsX ∧ Top.VolumeTheoremX := by
  intro hAI hU hBig hResK hSA hFHT hGaga hLine hQ hZ
  obtain ⟨hM, hKey, hSA', hSeg, hResK', _hSAst, hFHT', hGaga', _hSlope, hPB, hPHS, hPAn, hNine, _hAnti⟩ :=
    given_of_use hAI hU hBig hResK hSA hFHT hGaga hLine
  exact GlobalTheory.T.final_theorem_of_inputs_right hM hKey hSA' hSeg hResK' hFHT' hGaga' hLine hPB hPHS hPAn hNine
    (GlobalTheory.T.points_integrable_of_resolution_statement hResK) GlobalTheory.CompanionTheory.Ar.Giv.topAvoid hQ hZ GlobalTheory.thetaUnifAV_closed

end GlobalTheory.CompanionTheory.Ar.Link
