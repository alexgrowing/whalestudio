import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergSupSobolevSeminormThetaLaws
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
theorem _root_.GlobalTheory.T.heisenberg_sup_sobolev_seminorm_theta_laws : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ (S T : HSp D), (∀ k (f : WO S T → ℂ), IsThetaFunO ψ S T f → supSob ψ θ k f ≠ ⊤) ∧ (∀ (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ), (∀ U : AddSubgroup (WO S T), ∀ f ∈ GlobalTheory.Size.thetaLevel ψ S T U, dRho (heisO ψ S T) θ τ z f ∈ GlobalTheory.Size.thetaLevel ψ S T U) ∧ ∃ C : ℝ≥0, ∀ k (f : WO S T → ℂ), IsThetaFunO ψ S T f → supSob ψ θ k (dRho (heisO ψ S T) θ τ z f) ≤ C * supSob ψ θ (k + 1) f) ∧ ∀ k (f g : WO S T → ℂ) (c : ℂ), IsThetaFunO ψ S T f → IsThetaFunO ψ S T g → supSob ψ θ k (f + g) ≤ supSob ψ θ k f + supSob ψ θ k g ∧ supSob ψ θ k (c • f) = ‖c‖ₑ * supSob ψ θ k f := by
  first | exact @GlobalTheory.Unf.SupFin.supSob_laws | exact GlobalTheory.Unf.SupFin.supSob_laws | (intros; apply GlobalTheory.Unf.SupFin.supSob_laws <;> assumption)
