import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BoundedFunctionalThetaEstimate
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RealSizeNonneg
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bounded_functional_theta_estimate : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ (S T : HSp D) (m n : ℕ) (P : Mx D T.rank m) (Q : Mx D n S.rank) (N : ℕ), ∃ C : ℝ≥0, ∀ (ℓ : (WO S T → ℂ) → ℂ) (y : Mx D n m), (∀ f g, IsThetaFunO ψ S T f → IsThetaFunO ψ S T g → ℓ (f + g) = ℓ f + ℓ g) → (∀ (c : ℂ) f, IsThetaFunO ψ S T f → ℓ (c • f) = c * ℓ f) → (∀ f, IsThetaFunO ψ S T f → ‖ℓ f‖ₑ ≤ ⨆ w, ‖f w‖ₑ) → (∀ (ξ : Mx D m n) f, IsThetaFunO ψ S T f → ℓ (heisO ψ S T (P ⬝ ξ ⬝ Q) f) = ψ (-(Algebra.trace (AF D.host.F) (AE D) (y ⬝ ξ).trace)) * ℓ f) → ∀ f, IsThetaFunO ψ S T f → ‖ℓ f‖ₑ * ENNReal.ofReal ((1 + realSize θ y) ^ N) ≤ C * supSob ψ θ N f := by
  first | exact @GlobalTheory.CharDecay.decay | exact GlobalTheory.CharDecay.decay | (intros; apply GlobalTheory.CharDecay.decay <;> assumption)
