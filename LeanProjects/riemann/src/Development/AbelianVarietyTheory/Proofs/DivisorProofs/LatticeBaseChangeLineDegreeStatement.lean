import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeBaseChangeLineDegree
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
theorem _root_.GlobalTheory.T.lattice_base_change_line_degree : ∀ (K K' K'' : Type) [Field K] [NumberField K] [Field K'] [NumberField K'] [Field K''] [NumberField K''] [Algebra K K'] [Algebra K' K''] [Algebra K K''] [IsScalarTower K K' K''] (m : ℕ) (h : HermFam K (Fin m → K)) (h' : HermFam K' (Fin m → K')) (h'' : HermFam K'' (Fin m → K'')) (L : Submodule (𝓞 K) (Fin m → K)) (x : Fin m → K'), Full L → IsBC h h' → IsBC h h'' → Full (latBC K'' L) ∧ deg h'' (lineLat (latBC K'' L) (fun i => algebraMap K' K'' (x i))) = deg h' (lineLat (latBC K' L) x) := by
  first | exact @GlobalTheory.LineBCTower.lineLat_deg_tower | exact GlobalTheory.LineBCTower.lineLat_deg_tower | (intros; apply GlobalTheory.LineBCTower.lineLat_deg_tower <;> assumption)
