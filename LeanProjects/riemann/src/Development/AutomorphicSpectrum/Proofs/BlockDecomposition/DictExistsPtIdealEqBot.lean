import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianO1PullbackFubiniStudyMetric
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PointIdealMultiprojectivePrime
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemPointIdealIffEvalCoordsZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PointIdealHorizontalIffCharZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClosureDimIffArithmeticVarietyStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SpecializesIffPointIdealLeStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultiprojectivePrimeEqPointIdeal
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ComplexPointHasNonzeroLift
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermRepTensorProduct
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermRepDualInverse
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermRepTensorPower
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermRepTrivialLineBundle
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermRepOfIsometric
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermRepMetricSmooth
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermRepTwistedBundleExistsStatement
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

namespace GlobalTheory.CompanionTheory.MPDict

theorem dict_ptIdeal_injective {m : ℕ} (n : Fin (m + 1) → ℕ) :
    Function.Injective (ptIdeal : MP ℤ m n → Ideal (Geo.MRing (Bk n))) := fun x y h =>
  (((GlobalTheory.T.specializes_iff_point_ideal_le m n x y).2 h.le).antisymm ((GlobalTheory.T.specializes_iff_point_ideal_le m n y x).2 h.ge)).eq

end GlobalTheory.CompanionTheory.MPDict
