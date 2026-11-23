import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableGaussianExpLinearNormTermComplexMatrix
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjMono
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FockTransl
open Formalism.L2.Ker (VCx DVar derivAt0)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integrable_gaussian_exp_linear_norm_term_complex_matrix : ∀ (ι : Type) [Fintype ι] (a b : ℕ) (c : ι → ℝ), (∀ τ, 0 < c τ) → ∀ z₀ : VCx ι a b, Integrable fun z : VCx ι a b => Real.exp ((∑ k : DVar ι a b, ‖(c k.1 : ℂ) * z₀ k.1 k.2.1 k.2.2‖ * ‖z k.1 k.2.1 k.2.2‖) - gq c z / 2) := by
  first | exact @GlobalTheory.FockTransl.integrable_exp_lin_sub_gq | exact GlobalTheory.FockTransl.integrable_exp_lin_sub_gq | (intros; apply GlobalTheory.FockTransl.integrable_exp_lin_sub_gq <;> assumption)
