import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BottomExistsIntegrable
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BotTransfer

variable {D : D7} {T : Type} {A A' WW : HSp D}

theorem ker_smul (X : Tri T A A' WW) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (t : T) (κ : ℂ)
    (P : PolF D WW.rank A.rank) (h : GA D WW) (g : GA D A) :
    X.ker ψ θ t (κ • P) h g = κ * X.ker ψ θ t P h g := by
  simp only [Tri.ker, thetaKO, map_smul, Pi.smul_apply, smul_eq_mul]

theorem isConst_smul {X : Tri T A A' WW} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {c : T → ℂ}
    (h : X.IsConst ψ θ c) {κ : ℂ} (hκ : κ ≠ 0) : X.IsConst ψ θ fun t => κ * c t := by
  obtain ⟨⟨t₁, h₁⟩, P, P', H⟩ := h
  refine ⟨⟨t₁, mul_ne_zero hκ h₁⟩, κ • P, P', fun t => ⟨fun g => ⟨?_, ((H t).1 g).2⟩, (H t).2.1, fun g => ?_⟩⟩
  · have := ((H t).1 g).1.const_mul κ
    have e : X.ker ψ θ t (κ • P) g = fun x => κ * X.ker ψ θ t P g x := funext fun x => ker_smul X ψ θ t κ P g x
    rw [IntegrableOn, e]
    exact this
  · have e : X.I ψ θ t (κ • P) g = κ * X.I ψ θ t P g := by
      simp only [Tri.I, ker_smul, MeasureTheory.integral_const_mul]
    rw [e, (H t).2.2 g, mul_assoc]

end GlobalTheory.BotTransfer
