import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OmegaCentreLinear
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
theorem _root_.GlobalTheory.T.omega_centre_linear : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : WRep S T), IsInfFam θ → IsWeilDatumO ψ S T χS χT om → ∀ (τ : D.what₂.Tau) (z : MvPolynomial ℕ ℂ), (∀ f f', IsThetaFunO ψ S T f → IsThetaFunO ψ S T f' → omCentreT om θ τ z (f + f') = omCentreT om θ τ z f + omCentreT om θ τ z f') ∧ (∀ (c : ℂ) f, IsThetaFunO ψ S T f → omCentreT om θ τ z (c • f) = c • omCentreT om θ τ z f) ∧ ∀ f, IsThetaFunO ψ S T f → ∀ g h, thetaKO om g h (omCentreT om θ τ z f) = centreAct θ τ T z (fun h' => thetaKO om g h' f) h := by
  first | exact @GlobalTheory.Core.Rk.ZcComm.omCentreT_comm | exact GlobalTheory.Core.Rk.ZcComm.omCentreT_comm | (intros; apply GlobalTheory.Core.Rk.ZcComm.omCentreT_comm <;> assumption)
