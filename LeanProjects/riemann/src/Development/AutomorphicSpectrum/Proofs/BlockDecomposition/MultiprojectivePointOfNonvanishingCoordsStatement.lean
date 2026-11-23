import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultiprojectivePointOfNonvanishingCoords
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
theorem _root_.GlobalTheory.T.multiprojective_point_of_nonvanishing_coords : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (c : ∀ k, Bk n k) (z : (Σ k, Bk n k) → ℂ), (∀ k, z ⟨k, c k⟩ ≠ 0) →
  IsUnder (GlobalTheory.CompanionTheory.MPSmooth.multiprojectivePoint c z) z ∧ GlobalTheory.CompanionTheory.MPSmooth.multiprojectivePoint c z ∈ ptsIn (mpStr ℤ m n) σ₀ (mchart c) := by
  first | exact @GlobalTheory.CompanionTheory.MPSmooth.isUnder_ptMP | exact GlobalTheory.CompanionTheory.MPSmooth.isUnder_ptMP | (intros; apply GlobalTheory.CompanionTheory.MPSmooth.isUnder_ptMP <;> assumption)
