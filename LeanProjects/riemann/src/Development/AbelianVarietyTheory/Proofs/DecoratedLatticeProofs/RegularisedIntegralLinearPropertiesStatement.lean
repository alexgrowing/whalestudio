import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RegularisedIntegralLinearProperties
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
theorem _root_.GlobalTheory.T.regularised_integral_linear_properties : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S W W₀ : HSp D) (r' : ℕ) (d₀ : HypDec W W₀ r') (b' : GL (Fin W.rank) (AE D)) (χS χ : (AE D)ˣ →* Circle) (omh : WRep S W), IsInfFam θ → IsWeilDatumO ψ S W χS χ omh → ∀ mW : Measure (GA D W), EisensteinContinues d₀ b' → ∀ (τ : D.what₂.Tau) (zH : MvPolynomial ℕ ℂ) (P : Polynomial ℂ), (∀ φ', IsThetaFunO ψ S W φ' → RegIntProps ψ omh mW θ τ d₀ b' zH P φ') → (∀ f f', IsThetaFunO ψ S W f → IsThetaFunO ψ S W f' → ∀ g, regRes omh mW θ τ d₀ b' zH P (f + f') g = regRes omh mW θ τ d₀ b' zH P f g + regRes omh mW θ τ d₀ b' zH P f' g) ∧ ∀ (c : ℂ) f, IsThetaFunO ψ S W f → ∀ g, regRes omh mW θ τ d₀ b' zH P (c • f) g = c * regRes omh mW θ τ d₀ b' zH P f g := by
  first | exact @GlobalTheory.Core.Rk.regRes_linear | exact GlobalTheory.Core.Rk.regRes_linear | (intros; apply GlobalTheory.Core.Rk.regRes_linear <;> assumption)
