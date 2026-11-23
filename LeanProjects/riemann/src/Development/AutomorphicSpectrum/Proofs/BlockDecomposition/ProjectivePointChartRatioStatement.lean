import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProjectivePointChartRatio
import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ArakelovCycleHeights.QpSndStr
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ResidueDegreeOfIsClosedImmersion
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ArFormExists
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsPullHermPullLine
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MapPrBPtMP
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GlobalTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.projective_point_chart_ratio : ∀ (N : ℕ) (c : Fin (N + 1)) (w : Fin (N + 1) → ℂ), w c ≠ 0 →
  (∀ i, GlobalTheory.CompanionTheory.MPSmooth.ptP N c w ∈ ptsIn (PSpace.str ℤ N) σ₀ (chart ℤ N i) ↔ w i ≠ 0) ∧
  ∀ i j, GlobalTheory.CompanionTheory.MPSmooth.ptP N c w ∈ ptsIn (PSpace.str ℤ N) σ₀ (chart ℤ N i) →
    CxPts.ev (PSpace.str ℤ N) σ₀ (chart ℤ N i) (ratio ℤ N i j) (GlobalTheory.CompanionTheory.MPSmooth.ptP N c w) = w j / w i := by
  first | exact @GlobalTheory.CompanionTheory.MPSmooth.ptP_chart | exact GlobalTheory.CompanionTheory.MPSmooth.ptP_chart | (intros; apply GlobalTheory.CompanionTheory.MPSmooth.ptP_chart <;> assumption)
