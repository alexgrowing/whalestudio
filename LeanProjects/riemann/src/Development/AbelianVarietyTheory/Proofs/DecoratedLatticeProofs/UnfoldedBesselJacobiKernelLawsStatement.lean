import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnfoldedBesselJacobiKernelLaws
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.KerBF
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unfoldedBesselJacobiKernel_laws : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (s : StepBF ψ B J) (om' : Om B.V₀ J.W), IsWeilDatumO ψ B.V₀ J.W s.χV s.χW om' → ∀ (φ : GA D B.A → ℂ) (G : GA D J.W → ℂ) (Φ : WO B.V J.W → ℂ), IsContAut B.A φ → RapidDec J.W G → IsThetaFunO ψ B.V J.W Φ → Continuous (kerBF s φ G Φ) ∧ (∀ γ ∈ GQ J.W ⊓ jacGrp J.d, ∀ h, kerBF s φ G Φ (γ * h) = kerBF s φ G Φ h) ∧ (∀ γ ∈ GQ B.A, ∀ h₀ h, flatBF s (s.om (embA B.d B.o (γ * h₀), h) Φ) 0 = flatBF s (s.om (embA B.d B.o h₀, h) Φ) 0) ∧ ∀ h h' (n : flagN J.d), kerBF s φ G Φ (n.1 * J.d.emb0 h' * h) = fjAllFun ψ J.d B.o B.ζ s.om₀ B.vA.μ B.vA.𝓕 φ (rTrans h G) (flatBF s (s.om (1, h) Φ)) h' n := by
  first | exact @GlobalTheory.Unf.kerBF_laws | exact GlobalTheory.Unf.kerBF_laws | (intros; apply GlobalTheory.Unf.kerBF_laws <;> assumption)
