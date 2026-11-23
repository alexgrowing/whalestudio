import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaKernelIteratedIntegralsSwap
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaKernel_iterated_integrals_swap : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsInfFam θ → IsWeilDatumO ψ S T χS χT om → ∀ f, IsThetaFunO ψ S T f → ∀ (ν : Measure (GA D S)) (X : Set (GA D S)) (ν' : Measure (GA D T)) (X' : Set (GA D T)), ν.IsHaarMeasure → IsFundamentalDomain (GQ S) X ν → ν'.IsHaarMeasure → IsFundamentalDomain (GQ T) X' ν' → ∀ (G : GA D S → ℂ) (F : GA D T → ℂ), GlobalTheory.Grow.RapidDec S G → GlobalTheory.Grow.RapidDec T F → ∫ h in X', ∫ g in X, thetaKO om g h f * F h * conj (G g) ∂ν ∂ν' = ∫ g in X, ∫ h in X', thetaKO om g h f * F h * conj (G g) ∂ν' ∂ν := by
  first | exact @GlobalTheory.ChainOnto.ThetaSwap.integral_swap | exact GlobalTheory.ChainOnto.ThetaSwap.integral_swap | (intros; apply GlobalTheory.ChainOnto.ThetaSwap.integral_swap <;> assumption)
