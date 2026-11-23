import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SobContId
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HasDerivAtDOmT
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TameOfHeisDer
open scoped ComplexConjugate Matrix NNReal ENNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec delta ThetaClause)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
open GlobalTheory.Size (sobO thetaLevel)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ThetaDens

noncomputable section

namespace GlobalTheory.CenSob

open GlobalTheory.Chain.LiftReg GlobalTheory.Size

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}
  (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ))

variable (ψ θ) in

def Carried (L : (GA D T → ℂ) → (GA D T → ℂ)) : Prop :=
  ∃ (Δ : (WO S T → ℂ) → (WO S T → ℂ)) (r : ℕ), Tame ψ θ LinearMap.id r Δ ∧
    ∀ f, IsThetaFunO ψ S T f → ∀ g w, L (fun h => om (g, h) f w) = fun h => om (g, h) (Δ f) w

theorem theta_of_tame {r : ℕ} {Δ : (WO S T → ℂ) → (WO S T → ℂ)} (t : Tame ψ θ LinearMap.id r Δ)
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) : IsThetaFunO ψ S T (Δ f) :=
  t.theta (x := f) hf

theorem Carried.comp {L₁ L₂ : (GA D T → ℂ) → (GA D T → ℂ)} (h₁ : Carried ψ θ om L₁) (h₂ : Carried ψ θ om L₂) :
    Carried ψ θ om fun φ => L₁ (L₂ φ) := by
  obtain ⟨Δ₁, r₁, t₁, e₁⟩ := h₁
  obtain ⟨Δ₂, r₂, t₂, e₂⟩ := h₂
  refine ⟨fun f => Δ₁ (Δ₂ f), r₁ + r₂, t₁.comp t₂, fun f hf g w => ?_⟩
  beta_reduce
  rw [e₂ f hf g w, e₁ (Δ₂ f) (theta_of_tame t₂ hf) g w]

theorem Carried.add (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) {L₁ L₂ : (GA D T → ℂ) → (GA D T → ℂ)}
    (h₁ : Carried ψ θ om L₁) (h₂ : Carried ψ θ om L₂) : Carried ψ θ om fun φ => L₁ φ + L₂ φ := by
  obtain ⟨Δ₁, r₁, t₁, e₁⟩ := h₁
  obtain ⟨Δ₂, r₂, t₂, e₂⟩ := h₂
  refine ⟨fun f => Δ₁ f + Δ₂ f, max r₁ r₂, (t₁.mono (le_max_left _ _)).add hψ hθ (t₂.mono (le_max_right _ _)),
    fun f hf g w => ?_⟩
  beta_reduce
  rw [e₁ f hf g w, e₂ f hf g w]
  funext h
  simp only [Pi.add_apply, map_add]

theorem Carried.smul (c : ℂ) {L : (GA D T → ℂ) → (GA D T → ℂ)} (hL : Carried ψ θ om L) :
    Carried ψ θ om fun φ => c • L φ := by
  obtain ⟨Δ, r, t, e⟩ := hL
  refine ⟨fun f => c • Δ f, r, t.smul c, fun f hf g w => ?_⟩
  beta_reduce
  rw [e f hf g w]
  funext h
  simp only [Pi.smul_apply, map_smul]

end GlobalTheory.CenSob

end
