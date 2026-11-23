import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaIntegralMeasurableDefinite
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.LocalToGlobal.BesselHermitianTheta.TiedSmooth
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open scoped ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_integral_measurable_definite : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (Φ : WO S T → ℂ) (φ : GA D S → ℂ) (ν : Measure (GA D S)) (𝓕 : Set (GA D S)), GlobalTheory.FunPr.Hypotheses₂ → IsWeilDatumO ψ S T χS χT om → IsInfFam θ → IsThetaFunO ψ S T Φ → (∀ τ, (gramAt D S τ).PosDef) → (∀ τ, (gramAt D T τ).PosDef) → ν.IsHaarMeasure → IsFundamentalDomain (GQ S) 𝓕 ν → IsAutFunSm θ S φ → ∃ W : Submodule ℂ (GA D T → ℂ), FiniteDimensional ℂ W ∧ (fun h : GA D T => ∫ g in 𝓕, thetaKO om g h Φ * φ g ∂ν) ∈ W ∧ ∀ τ k, ∀ f ∈ W, gelf θ T τ k f ∈ W := by
  first | exact @GlobalTheory.DefiniteLiftZfin.lift_zfin | exact GlobalTheory.DefiniteLiftZfin.lift_zfin | (intros; apply GlobalTheory.DefiniteLiftZfin.lift_zfin <;> assumption)
