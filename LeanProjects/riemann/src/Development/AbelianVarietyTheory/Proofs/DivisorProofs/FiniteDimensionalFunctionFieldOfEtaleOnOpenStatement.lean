import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalFunctionFieldOfEtaleOnOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionFieldMapCompConstFn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NadelVanishingCanonicalAddBoundary
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteDimensional_functionField_of_etale_on_open' : ∀ (M W : Scheme.{0}) [IsIntegral M] [IsIntegral W] (f : M ⟶ W) [IsDominant f] (U : M.Opens), Etale (U.ι ≫ f) → (U : Set M).Nonempty → letI := (functionFieldMap f).toAlgebra; FiniteDimensional W.functionField M.functionField := by
  first | exact @GlobalTheory.FunctionFieldEtale.finiteDimensional_functionField_of_etale_on_open | exact GlobalTheory.FunctionFieldEtale.finiteDimensional_functionField_of_etale_on_open | (intros; apply GlobalTheory.FunctionFieldEtale.finiteDimensional_functionField_of_etale_on_open <;> assumption)
