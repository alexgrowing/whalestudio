import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaKillWittDecomposition
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
theorem _root_.GlobalTheory.T.theta_kill_witt_decomposition : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A : HSp D) (cA : CptF A) (a : GL (Fin A.rank) (AE D)), Defin θ A cA a → ∀ (W W₀ : HSp D) (r' : ℕ) (d₀ : HypDec W W₀ r') (b' : GL (Fin W.rank) (AE D)) (χ : (AE D)ˣ →* Circle) (omh : WRep (dblSp A) W), IsWeilDatumO ψ (dblSp A) W 1 χ omh → ∀ (m : Measure (GA D A)) (mW : Measure (GA D W)), m.IsHaarMeasure → mW.IsHaarMeasure → ∀ u : GA D A → ℂ, Continuous u → (∀ γ ∈ GQ A, ∀ g, u (γ * g) = u g) → Kills ψ χ omh m u → EisensteinContinues d₀ b' → ∀ (τ : D.what₂.Tau) (zH : MvPolynomial ℕ ℂ) (P : Polynomial ℂ), P ≠ 0 → (∀ φ', IsThetaFunO ψ (dblSp A) W φ' → RegIntProps ψ omh mW θ τ d₀ b' zH P φ') → ∀ φ, IsThetaFunO ψ (dblSp A) W φ → IsKFinVec omh (Khat A a) φ → GlobalTheory.Eis.dblInt A χ⁻¹ m (regRes omh mW θ τ d₀ b' zH P φ) (fun g => conj (u g)) (fun g => conj (u g)) = 0 := by
  first | exact @GlobalTheory.Core.Rk.RegKill.dblInt_regRes_eq_zero | exact GlobalTheory.Core.Rk.RegKill.dblInt_regRes_eq_zero | (intros; apply GlobalTheory.Core.Rk.RegKill.dblInt_regRes_eq_zero <;> assumption)
