import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeisOAdd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaIntegrandIntegrable
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite

noncomputable section

open scoped ComplexOrder

namespace GlobalTheory.DownLift.GenFinite

theorem thetaKO_smul {D : D7} {S T : HSp D} (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (h : GA D S)
    (g : GA D T) (c : ℂ) (f : WO S T → ℂ) : thetaKO om h g (c • f) = c * thetaKO om h g f := by
  simp only [thetaKO, map_smul, Pi.smul_apply, smul_eq_mul]

theorem integrableOn_downIntegrand : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type)
    (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP →
    ∀ (i : Fin D.R.m) (t : T) (y : (R.HV i t).H) (f : WO (Vc D i) (Wc D i) → ℂ) (l : (R.cV i).W →ₗ[ℂ] ℂ)
      (g : GA D (Wc D i)), IsThetaFunO R.ψ (Vc D i) (Wc D i) f →
      IntegrableOn (fun h => thetaKO (R.ωP i t) h g f * l (R.extV i t y h)) (R.fdV i t) (R.νV i t) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hG hP i t y f l g hf
  have hm := hG.core.models
  have hom := (hP i t).datum
  have hx := (hm.HV i t).2.1.le (LinearMap.mem_range_self _ y)
  have hpos : ∀ τ, (gramAt D (Vc D i) τ).PosDef := fun τ => by
    have := D.sp.V_sig ((i : ℕ) + 1) (tauE D τ)
    rw [hm.vpos i] at this
    exact GlobalTheory.DefiniteQuotient.posDef_of_signature this
  have hcont : Continuous fun h => l (R.extV i t y h) :=
    (LinearMap.continuous_of_finiteDimensional l).comp
      (GlobalTheory.ThetaIntegrand.ext_continuous (R.cV i) (hm.cV i) (R.βV i) (R.datVt i t) hx)
  have hinv : ∀ γ ∈ GQ (Vc D i), ∀ h, l (R.extV i t y (γ * h)) = l (R.extV i t y h) := fun γ hγ h =>
    congrArg l (GlobalTheory.ThetaIntegrand.ext_invariant (R.cV i) hx γ hγ h)
  have key := GlobalTheory.DefiniteQuotient.integrableOn_theta D R.ψ hom.std (Vc D i) (Wc D i) _ _ (R.ωP i t) hom hpos ℂ
    (LinearMap.smulRight (LinearMap.id : ℂ →ₗ[ℂ] ℂ) f) (fun x => theta_smul x hf) (fun h => l (R.extV i t y h)) hcont hinv
    (R.νV i t) (R.fdV i t) (hm.νV i t).1.1 (hm.νV i t).2 g
  have e : (fun h => thetaKO (R.ωP i t) h g (LinearMap.smulRight (LinearMap.id : ℂ →ₗ[ℂ] ℂ) f (l (R.extV i t y h)))) =
      fun h => thetaKO (R.ωP i t) h g f * l (R.extV i t y h) := by
    funext h
    exact (thetaKO_smul (R.ωP i t) h g _ f).trans (mul_comm _ _)
  rw [e] at key
  exact key

end GlobalTheory.DownLift.GenFinite

end
