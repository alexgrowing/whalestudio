import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RealActionRational

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.Cx

namespace GlobalTheory.Proof.RealFockActionTwistedOperators

open GlobalTheory.IndefiniteRowSideFullHecke.RealActionRational

theorem thetaKO_rat_mul {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hom : IsWeilDatumO ψ S T χS χT om) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) {γ : GA D S} (hγ : γ ∈ GQ S) (h : GA D S) (g : GA D T) :
    thetaKO om (γ * h) g f = thetaKO om h g f := by
  unfold thetaKO
  have hp : ((γ * h, g) : GA D S × GA D T) = (γ, 1) * (h, g) := by simp
  rw [hp, map_mul, Module.End.mul_apply]
  exact hom.om_aut γ hγ 1 (one_mem _) _ (hom.om_pres _ _ hf)

theorem thetaKO_mul_right {D : D7} {S T : HSp D} (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ))
    (f : WO S T → ℂ) (h u : GA D S) (g : GA D T) :
    thetaKO om (h * u) g f = thetaKO om h g (om (u, 1) f) := by
  unfold thetaKO
  have hp : ((h * u, g) : GA D S × GA D T) = (h, g) * (u, 1) := by simp
  rw [hp, map_mul, Module.End.mul_apply]

theorem adForms_rat {G Γ W : Type} [Group G] [Group Γ] (ι : Γ →* G) [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    {ρ : Γ →* Module.End ℂ W} {J : Subgroup G} {χ : J →* ℂˣ} {f : G → W} (hf : f ∈ Bridge.AdForms ι ρ J χ)
    (γ : Γ) (h : G) : f (ι γ * h) = ρ γ (f h) := by
  have h1 : f (ι γ * h * ((1 : J) : G)) = (χ 1 : ℂ) • ρ γ (f h) := hf γ h 1
  simpa using h1

theorem form_rat {D : D7} {V : HSp D} (c : CoefA V) {J : Subgroup (Bridge.Gf V)} {χ : J →* ℂˣ}
    {f : Bridge.Gf V → c.W} (hf : f ∈ Bridge.AdForms (Bridge.ratF V) c.coef.ρ J χ) {γ : GA D V} (hγ : γ ∈ GQ V)
    (h : GA D V) : c.ext f (γ * h) = c.ρ (γ * h)⁻¹ (c.ρ γ (f ((finHom V).rangeRestrict h))) := by
  show c.ρ (γ * h)⁻¹ (f ((finHom V).rangeRestrict (γ * h))) = _
  congr 1
  have hr : (finHom V).rangeRestrict (γ * h) = Bridge.ratF V ⟨γ, hγ⟩ * (finHom V).rangeRestrict h := by
    apply Subtype.ext
    simp [Bridge.ratF]
  rw [hr, adForms_rat (Bridge.ratF V) hf ⟨γ, hγ⟩]
  rfl

theorem ext_mul_real {D : D7} {V : HSp D} (c : CoefA V) (f : Bridge.Gf V → c.W) {u : GA D V} (hu : u ∈ GinfC V)
    (h : GA D V) : c.ext f (h * u) = c.ρ (h * u)⁻¹ (f ((finHom V).rangeRestrict h)) := by
  have hu' : finHom V u = 1 := hu
  have hr : (finHom V).rangeRestrict (h * u) = (finHom V).rangeRestrict h := by
    apply Subtype.ext
    simp [hu']
  show c.ρ (h * u)⁻¹ (f ((finHom V).rangeRestrict (h * u))) = _
  rw [hr]

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m) (t : T)

end GlobalTheory.Proof.RealFockActionTwistedOperators

end
