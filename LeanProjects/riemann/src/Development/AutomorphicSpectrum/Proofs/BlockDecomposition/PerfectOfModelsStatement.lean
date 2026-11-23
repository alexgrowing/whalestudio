import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PerfectOfModels
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.CubeTheorem.LBSpreads
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsProjOverOfIsProjOverBase
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CubeTheorem
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.SpreadingModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.perfect_of_models : (∀ (R : Type) [CommRing R] (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of R)), Smooth f → IsProper f → ∀ M : LB Y, M.IsLB → GlobalTheory.SpreadingModels.HasModel f M) → GlobalTheory.SpreadingModels.PerfAll := by
  first | exact @GlobalTheory.CompanionTheory.SpreadingModels.perfAll_of_hasModel | exact GlobalTheory.CompanionTheory.SpreadingModels.perfAll_of_hasModel | (intros; apply GlobalTheory.CompanionTheory.SpreadingModels.perfAll_of_hasModel <;> assumption)
