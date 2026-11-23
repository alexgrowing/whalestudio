import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RegularisedThetaPairingIdentity
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
theorem _root_.GlobalTheory.T.regularised_theta_pairing_identity : GlobalTheory.Published.DoublingMethod → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A B : HSp D) (χA χB : (AE D)ˣ →* Circle) (sA : RealMat A) (sB : RealMat B) (t : ℕ) (cA : CptF A) (a : GL (Fin A.rank) (AE D)) (om : WRep A B) (ν : Measure (WO A B)) (𝓕 : Set (WO A B)), Pair ψ θ A B χA χB sA sB t cA a om ν 𝓕 → ∀ omh : WRep (dblSp A) B, IsWeilDatumO ψ (dblSp A) B 1 χB omh → ∀ m : Measure (GA D A), m.IsHaarMeasure → ∀ Φ, IsFockVec ψ θ A B sA sB Φ → ∀ u ∈ A0 θ A cA, GlobalTheory.Eis.IsZetaFamily A χB⁻¹ m (flat A a (swSec A B omh ν 𝓕 (delta A B Φ Φ)) (sZero A B)) (fun g => conj (u g)) (fun g => conj (u g)) ∧ GlobalTheory.Eis.EisContinues A (flat A a (swSec A B omh ν 𝓕 (delta A B Φ Φ)) (sZero A B)) ∧ (∀ g, AnalyticOnNhd ℂ (GlobalTheory.Eis.eisSer A (flat A a (swSec A B omh ν 𝓕 (delta A B Φ Φ)) (sZero A B)) g) (rightOf (A.rank / 2))) ∧ (∀ s₀, ∃ k, GlobalTheory.Eis.EisRegularAt A (flat A a (swSec A B omh ν 𝓕 (delta A B Φ Φ)) (sZero A B)) s₀ k) ∧ ∀ s : ℂ, (A.rank : ℝ) / 2 < s.re → Integrable (integrand om m ν 𝓕 (frameLat A) a Φ Φ u u s) m ∧ GlobalTheory.Eis.zeta A χB⁻¹ m (flat A a (swSec A B omh ν 𝓕 (delta A B Φ Φ)) (sZero A B)) (fun g => conj (u g)) (fun g => conj (u g)) s = ∫ g, integrand om m ν 𝓕 (frameLat A) a Φ Φ u u s g ∂m := by
  first | exact @GlobalTheory.Core.Rk.Exh.zeta_eq_integral_integrand | exact GlobalTheory.Core.Rk.Exh.zeta_eq_integral_integrand | (intros; apply GlobalTheory.Core.Rk.Exh.zeta_eq_integral_integrand <;> assumption)
