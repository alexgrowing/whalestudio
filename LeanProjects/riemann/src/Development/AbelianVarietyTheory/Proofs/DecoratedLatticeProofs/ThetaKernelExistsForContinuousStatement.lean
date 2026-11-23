import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaKernelExistsForContinuous
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PrinInf
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SkewGramHalfModule
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLPartialContinuationHolds
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_kernel_exists_for_continuous : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A : HSp D) (cA : CptF A) (a : GL (Fin A.rank) (AE D)), Defin θ A cA a → ∀ (W : HSp D) (χ : (AE D)ˣ →* Circle) (omh : WRep (dblSp A) W), IsWeilDatumO ψ (dblSp A) W 1 χ omh → ∀ φ, IsThetaFunO ψ (dblSp A) W φ → IsKFinVec omh (Khat A a) φ → ∀ m : Measure (GA D A), m.IsHaarMeasure → ∀ u : GA D A → ℂ, Continuous u → (∀ γ ∈ GQ A, ∀ g, u (γ * g) = u g) → ∃ φ', IsThetaFunO ψ (dblSp A) W φ' ∧ ∀ Λ : (WO (dblSp A) W → ℂ) → ℂ, (∀ f f', IsThetaFunO ψ (dblSp A) W f → IsThetaFunO ψ (dblSp A) W f' → Λ (f + f') = Λ f + Λ f') → (∀ (c : ℂ) f, IsThetaFunO ψ (dblSp A) W f → Λ (c • f) = c * Λ f) → (∀ γ ∈ GQ (dblSp A), ∀ g, Λ (omh (γ * g, 1) φ) = Λ (omh (g, 1) φ)) → GlobalTheory.Eis.dblInt A χ⁻¹ m (fun g => Λ (omh (g, 1) φ)) (fun g => conj (u g)) (fun g => conj (u g)) = Λ φ' := by
  first | exact @GlobalTheory.Core.Rk.Collect.dblInt_collect | exact GlobalTheory.Core.Rk.Collect.dblInt_collect | (intros; apply GlobalTheory.Core.Rk.Collect.dblInt_collect <;> assumption)
