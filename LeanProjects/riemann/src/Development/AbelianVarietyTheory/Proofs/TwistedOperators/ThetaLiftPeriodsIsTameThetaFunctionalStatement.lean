import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftPeriodsIsTameThetaFunctional
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.PartFixed
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaLift_periods_isTameThetaFunctional : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (W : HSp D) (vW : GlobalTheory.Unf.Vol W) (G : GA D W → ℂ), RapidDec W G → (∀ (ρ : ℕ) (B : BesL D ρ) (χ χ' : (AE D)ˣ →* Circle) (om : Om B.V W), IsWeilDatumO ψ B.V W χ χ' om → ∀ φ, RapidDec B.A φ → Tame ψ B.V W fun Φ => B.per ψ φ (liftS om vW.μ vW.𝓕 G Φ)) ∧ ∀ (ρ : ℕ) (J : JacL D ρ) (χ χ' : (AE D)ˣ →* Circle) (om : Om J.W W), IsWeilDatumO ψ J.W W χ χ' om → ∀ (L' : HSp D) (ζ' : Fin L'.rank → D.host.E) (χ₁ χ₂ : (AE D)ˣ →* Circle) (omz : Om J.W₀ L'), IsWeilDatumO ψ J.W₀ L' χ₁ χ₂ omz → ∀ φ Φ₀, RapidDec J.W₀ φ → IsThetaFunO ψ J.W₀ L' Φ₀ → Tame ψ J.W W fun Φ => J.per ψ ζ' omz φ (liftS om vW.μ vW.𝓕 G Φ) Φ₀ := by
  first | exact @GlobalTheory.LiftTame.lift_periods_tame | exact GlobalTheory.LiftTame.lift_periods_tame | (intros; apply GlobalTheory.LiftTame.lift_periods_tame <;> assumption)
