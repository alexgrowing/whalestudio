import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PairedThetaKernelContinuousAndRationallyInvarian
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pairedThetaKernel_continuous_and_rationally_invariant : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (J : JacLev D (σ + 1)) (B : BesLev D σ) (s : StepFB ψ J B) (vL : VolM D B.L.rank J.W₀.rank) (Y : GA D J.W₀ → WO J.W₀ B.L → ℂ) (Ξ : WO J.W₀ B.V₀ → ℂ), IsQuasiFam ψ J.W₀ B.L Y → IsThetaFunO ψ J.W₀ B.V₀ Ξ → Continuous (Function.uncurry (pairKer s vL Y Ξ)) ∧ (∀ γ ∈ GQ J.W₀, ∀ h₀ h₁, pairKer s vL Y Ξ (γ * h₀) h₁ = pairKer s vL Y Ξ h₀ h₁) ∧ ∀ γ ∈ GQ B.A, ∀ h₀ h₁, pairKer s vL Y Ξ h₀ (γ * h₁) = pairKer s vL Y Ξ h₀ h₁ := by
  first | exact @GlobalTheory.PairKer.pairKer_law | exact GlobalTheory.PairKer.pairKer_law | (intros; apply GlobalTheory.PairKer.pairKer_law <;> assumption)
