import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSpecializesDominatesStalkOfRegular
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionFieldMapCompConstFn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NadelVanishingCanonicalAddBoundary
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_specializes_dominatesStalk_of_regular : ∀ (X : Scheme.{0}) [IsIntegral X] (V : ValuationSubring X.functionField) (y : X), (∀ g, RegAt y g → g ∈ V) → ∃ z, z ⤳ y ∧ DominatesStalk V z := by
  first | exact @GlobalTheory.exists_specializes_dominatesStalk_of_regAt | exact GlobalTheory.exists_specializes_dominatesStalk_of_regAt | (intros; apply GlobalTheory.exists_specializes_dominatesStalk_of_regAt <;> assumption)
