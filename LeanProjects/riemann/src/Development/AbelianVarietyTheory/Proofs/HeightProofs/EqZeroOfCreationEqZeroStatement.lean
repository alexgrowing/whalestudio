import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EqZeroOfCreationEqZero
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.StarPurelyImaginaryEqNeg
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_zero_of_hD_sub_I_smul_hD_eq_zero_of_bounded : ∀ (G R : Type) [AddCommGroup G] [NormedAddCommGroup R] [NormedSpace ℝ R] [FiniteDimensional ℝ R] (ι : R →+ G) (π : G →+ R) (om : R →ₗ[ℝ] R →ₗ[ℝ] ℝ), (∀ x, π (ι x) = x) → (∀ (f : G → ℂ), Sm ι f → ∀ (u : R) (w : G), hD ι π om u f w = -(Real.pi * Complex.I) * (om (π w) u : ℝ) * f w + fderiv ℝ (fun x : R => f (w + ι x)) 0 u) → (∀ u v, om v u = -om u v) → ∀ (f : G → ℂ), Sm ι f → (∀ w, ∃ C : ℝ, ∀ x, ‖f (w + ι x)‖ ≤ C) → ∀ u u' : R, 0 < om u u' → hD ι π om u f - Complex.I • hD ι π om u' f = 0 → f = 0 := by
  first | exact @GlobalTheory.FockCompare.eq_zero_of_creation_eq_zero | exact GlobalTheory.FockCompare.eq_zero_of_creation_eq_zero | (intros; apply GlobalTheory.FockCompare.eq_zero_of_creation_eq_zero <;> assumption)
