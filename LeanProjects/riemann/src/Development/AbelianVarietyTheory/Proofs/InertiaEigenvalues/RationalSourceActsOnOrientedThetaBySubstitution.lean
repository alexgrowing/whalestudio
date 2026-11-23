import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWeilDatumOOneOfRankZero
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfPartOneSubEInfSmul

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open GlobalTheory.RawLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RatSubst

theorem om_rat_left_apply : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (ω : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT ω → ∀ f, IsThetaFunO ψ S T f → ∀ γ ∈ GQ S, ∀ x, ω (γ, 1) f x = f (actO S T γ⁻¹ 1 x) := by
  intro D ψ S T χS χT ω hω f hf γ hγ x
  have h := GlobalTheory.SiegelFormula.om_rat_apply hω hγ (one_mem (GQ T)) (actO S T γ⁻¹ 1 x) hf
    (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hω.std hf _)
  have e : actO S T γ 1 (actO S T γ⁻¹ 1 x) = x := by
    have h1 : Formalism.L2.Theta.mt T 1 = 1 := rfl
    have h2 : Formalism.L2.Theta.mt S γ * Formalism.L2.Theta.mt S γ⁻¹ = 1 := by
      have : Formalism.L2.Theta.mt S (γ * γ⁻¹) = Formalism.L2.Theta.mt S γ * Formalism.L2.Theta.mt S γ⁻¹ := rfl
      rw [← this, mul_inv_cancel]; rfl
    unfold actO
    rw [inv_inv, h1, Matrix.one_mul, Matrix.one_mul, Matrix.mul_assoc, h2, Matrix.mul_one]
  rwa [e] at h

end GlobalTheory.RatSubst
