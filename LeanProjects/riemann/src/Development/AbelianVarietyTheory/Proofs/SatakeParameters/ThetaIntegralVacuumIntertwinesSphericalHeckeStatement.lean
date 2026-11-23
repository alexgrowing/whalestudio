import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaIntegralVacuumIntertwinesSphericalHecke
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaIntegral_vacuum_intertwines_sphericalHecke : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (P : Pl D.host.E), IsWeilDatumO ψ S T χS χT om → ∀ (ν : Measure (GA D T)) (𝓕 : Set (GA D T)), ν.IsHaarMeasure → IsFundamentalDomain (GQ T) 𝓕 ν → VacFix ψ om P → ∀ cS cT, Match ψ om P cS (dualC cT) → ∀ f, IsVacAt ψ S T P f → ∀ Φ : GA D T → ℂ, (∀ γ ∈ GQ T, ∀ h, Φ (γ * h) = Φ h) → (∀ k ∈ hyp T P, ∀ h, Φ (h * k) = Φ h) → (∀ g, ∀ y ∈ GfC T, IntegrableOn (fun h => thetaKO om g h f * Φ (h * y)) 𝓕 ν) → Lift.liftInt ν 𝓕 (thetaKO om) f (hk T P cT Φ) = hk S P cS (Lift.liftInt ν 𝓕 (thetaKO om) f Φ) := by
  first | exact @GlobalTheory.ThetaIntHecke.liftInt_hk | exact GlobalTheory.ThetaIntHecke.liftInt_hk | (intros; apply GlobalTheory.ThetaIntHecke.liftInt_hk <;> assumption)
