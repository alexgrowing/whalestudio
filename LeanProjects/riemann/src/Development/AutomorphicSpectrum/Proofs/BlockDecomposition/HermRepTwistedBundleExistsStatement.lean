import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermRepTwistedBundleExists
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsPullHermPullLine
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedA
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Birational
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.IsSmoothHermConstLine

set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict
open GlobalTheory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermRep_twisted_bundle_exists : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (M : HermLB (mpStr ℤ m n)) (c : Fin m) (t : ℤ), Nonempty (LBIso M.B (twB m n c t)) → ∃ A : Geo.HermLine (Bk n), IsHermRep M A ∧ A.a = Pi.single c.succ 1 + t • Pi.single 0 1 := by
  first | exact @GlobalTheory.CompanionTheory.MPDict.TwLine.exists_hermLine_of_twB | exact GlobalTheory.CompanionTheory.MPDict.TwLine.exists_hermLine_of_twB | (intros; apply GlobalTheory.CompanionTheory.MPDict.TwLine.exists_hermLine_of_twB <;> assumption)
