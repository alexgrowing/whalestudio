import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeStdSublatticeNonpos
import Development.AbelianVarietyTheory.Definitions.Divisors.SecJets4
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.PosSemidefOfForallCombination
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.InhabSt
open NumberField MeasureTheory ReciprocityTheory.GeometryOfNumbersTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LieHt
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.degree_std_sublattice_nonpos : ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (W : Submodule (𝓞 K) (Fin n → K)), W ≤ stdLat K n → deg (stdHerm K n) W ≤ 0 := by
  first | exact @GlobalTheory.StdLatDeg.deg_le_zero_of_le_stdLat | exact GlobalTheory.StdLatDeg.deg_le_zero_of_le_stdLat | (intros; apply GlobalTheory.StdLatDeg.deg_le_zero_of_le_stdLat <;> assumption)
