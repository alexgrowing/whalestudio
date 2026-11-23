import Development.AbelianVarietyTheory.Definitions.Divisors.KeyPBIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SummableNormMulPowOfBounded
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.SummableNormBoundedSeries
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.MBLow.BddPS

def bdd (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] : Subring (PowerSeries C) :=
  GlobalTheory.BoundedPowerSeriesDisc.boundedSeries C

variable {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C]

noncomputable def ev [CompleteSpace C] (π : C) (h : ‖π‖ < 1) : bdd C →+* C :=
  GlobalTheory.BoundedPowerSeriesDisc.evalBounded π h

theorem main : ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] (π : C), ‖π‖ < 1 → ∃ (B : Subring (PowerSeries C)) (ev : B →+* C) (t : B), (∀ Φ, Φ ∈ B ↔ ∃ b : ℝ, ∀ n, ‖PowerSeries.coeff n Φ‖ ≤ b) ∧ (∀ Φ : B, ev Φ = ∑' n, PowerSeries.coeff n (Φ : PowerSeries C) * π ^ n) ∧ t ≠ 0 ∧ (∀ Φ, ev Φ = 0 ↔ t ∣ Φ) ∧ ∀ Φ : B, Φ ≠ 0 → ∃ n : ℕ, ¬ t ^ n ∣ Φ := by
  first
  | (run_tac Lean.Elab.Tactic.liftMetaTactic (fun g => do pure [← g.revertAll])); exact @_root_.GlobalTheory.SummableSeriesBounds.main
  | (run_tac Lean.Elab.Tactic.liftMetaTactic (fun g => do pure [← g.revertAll])); exact _root_.GlobalTheory.SummableSeriesBounds.main
  | exact @_root_.GlobalTheory.SummableSeriesBounds.main
  | exact _root_.GlobalTheory.SummableSeriesBounds.main
  | (apply _root_.GlobalTheory.SummableSeriesBounds.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.SummableSeriesBounds.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SummableSeriesBounds.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SummableSeriesBounds.main ..)

end GlobalTheory.MBLow.BddPS
