import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinearIndependentRealCombinationsOfIndependent
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsLatBasisZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpanPeriodLatticeComplexSemiAbelianEqTopStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linearIndependent_real_combinations_of_independent : ∀ (g r d : ℕ) (x : Fin r → Fin g → ℂ) (e : Fin d → Fin r → ℝ), LinearIndependent ℝ x → LinearIndependent ℝ e → LinearIndependent ℝ (fun i => ∑ m, (e i m : ℂ) • x m) := by
  first | exact @GlobalTheory.linearIndependent_real_combination | exact GlobalTheory.linearIndependent_real_combination | (intros; apply GlobalTheory.linearIndependent_real_combination <;> assumption)
