import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineDegreeLowerBound
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SecJets4
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ConjInvIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogHeightBoundFromInequalityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianLatticeBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiFibrationLieLatticeFullStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetSlopeDegreeInequalityStatement
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.PosSemidefOfForallCombination
import ReciprocityTheory.GeometryOfNumbers.MatrixArithmetic.WeakMatSt
open NumberField MeasureTheory ReciprocityTheory.GeometryOfNumbersTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LieHt
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_line_degree_lower_bound : GlobalTheory.Published.AbsoluteSiegel → ∀ (K : Type) [Field K] [NumberField K] (m : ℕ) (h : HermFam K (Fin m → K)) (L W : Submodule (𝓞 K) (Fin m → K)), Full L → GlobalTheory.Published.ConjInv h → W ≤ L → 1 ≤ latRank K W → ∃ (K' : Type) (_ : Field K') (_ : NumberField K') (_ : Algebra K K') (h' : HermFam K' (Fin m → K')) (x : Fin m → K'), IsBC h h' ∧ x ≠ 0 ∧ deg h W / latRank K W - Real.log (latRank K W) / 2 - 1 ≤ deg h' (lineLat (latBC K' L) x) := by
  first | exact @GlobalTheory.siegel_sublattice_line | exact GlobalTheory.siegel_sublattice_line | (intros; apply GlobalTheory.siegel_sublattice_line <;> assumption)
