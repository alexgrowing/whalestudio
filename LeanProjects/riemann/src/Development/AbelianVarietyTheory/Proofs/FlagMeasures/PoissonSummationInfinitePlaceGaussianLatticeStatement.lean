import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PoissonSummationInfinitePlaceGaussianLattice
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsLatMeasurableConst
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.poisson_summation_infinitePlaceGaussian_lattice : ∀ (E : Type) [Field E] [NumberField E] (j : ℕ) (L : Submodule ℤ (VecInf E j)) [DiscreteTopology L], IsZLattice ℝ L → Summable (fun x : L => gaussV E j x) ∧ Summable (fun y : dualAt E j L => gaussV E j y) ∧ ∑' x : L, gaussV E j x = (covAt E j L)⁻¹ * ∑' y : dualAt E j L, gaussV E j y ∧ ∫ x, gaussV E j x = 1 := by
  first | exact @GlobalTheory.FlagBase.poisson_gaussV | exact GlobalTheory.FlagBase.poisson_gaussV | (intros; apply GlobalTheory.FlagBase.poisson_gaussV <;> assumption)
