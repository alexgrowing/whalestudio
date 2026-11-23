import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultiprojectiveChartHolomorphicCoordinates
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
theorem _root_.GlobalTheory.T.multiprojective_chart_holomorphic_coordinates : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (c : ∀ k, Bk n k), IsAffineOpen (mchart c) ∧
  ∀ a : Γ(MP ℤ m n, mchart c), DifferentiableOn ℂ (CxPts.ev (mpStr ℤ m n) σ₀ (mchart c) a ∘ GlobalTheory.CompanionTheory.MPSmooth.multiprojectivePoint c)
    {z | ∀ k, z ⟨k, c k⟩ ≠ 0} := by
  first | exact @GlobalTheory.CompanionTheory.MPSmooth.mchart_affine_holo | exact GlobalTheory.CompanionTheory.MPSmooth.mchart_affine_holo | (intros; apply GlobalTheory.CompanionTheory.MPSmooth.mchart_affine_holo <;> assumption)
