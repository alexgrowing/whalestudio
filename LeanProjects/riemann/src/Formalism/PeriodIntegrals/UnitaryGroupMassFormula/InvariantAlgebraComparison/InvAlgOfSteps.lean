import Mathlib
import Formalism.PeriodIntegrals.AdBridgeSteps

noncomputable section

namespace PI.UnitaryGroupMassFormula.BridgeInvAlg

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct
open Formalism.MainNotions.S (AutInst uMat)
open Formalism.L2.SG.AdBridge

def Theta (I : AutInst) : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F ⊗[I.F] I.E →+*
    (InfinitePlace I.F → ℂ) × (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) :=
  RingHom.prod (Pi.ringHom fun v => thetaV I v) (tauF I)

theorem theta_apply (I : AutInst) (x : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F ⊗[I.F] I.E) :
    Theta I x = (fun v => thetaV I v x, tauF I x) := rfl

def ThetaInj : Prop := ∀ I : AutInst, Function.Injective (Theta I)

def ThetaSurj : Prop := ∀ I : AutInst, Function.Surjective (Theta I)

def HomStep : Prop := ∀ I : AutInst, ∃ f : HAd I →* I.GA, PI.AdBridgeSteps.IsFormula I f

def InjStep : Prop := ∀ (I : AutInst) (f : HAd I →* I.GA), PI.AdBridgeSteps.IsFormula I f →
  Function.Injective f

def SurjStep : Prop := ∀ (I : AutInst) (f : HAd I →* I.GA), PI.AdBridgeSteps.IsFormula I f →
  Function.Surjective f

end PI.UnitaryGroupMassFormula.BridgeInvAlg
