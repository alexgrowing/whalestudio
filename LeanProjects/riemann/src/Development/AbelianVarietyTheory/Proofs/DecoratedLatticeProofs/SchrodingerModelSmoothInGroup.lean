import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HasDerivAtDOmT
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelWeilSectionIntegrableAndContinuous
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchrodingerFunctionLinearThetaFunctions
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemSmoothFunctionsOfClosedRightDerivatives
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MeanPair
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.RegularisingElement
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.EisensteinResidue
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.FirstTermIdentitySchrodinger
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.EisensteinMaximalParabolic
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelEisensteinPolesStd
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelEisensteinSimplePoleOfDoublingMethod
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DifferentiableOneP
open scoped Matrix NNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Core.Rk.SchCen

open GlobalTheory.IndefiniteRowSideFullHecke.RapidDecayLift (dOmS)
open Filter Topology

variable {D : D7} (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ))
  (θ : InfFam D)

def Adapted (L : (WO S T → ℂ) → ℂ) : Prop :=
  (∀ f f', IsThetaFunO ψ S T f → IsThetaFunO ψ S T f' → L (f + f') = L f + L f') ∧
  (∀ (c : ℂ) f, IsThetaFunO ψ S T f → L (c • f) = c * L f) ∧
  ∀ f, IsThetaFunO ψ S T f → ∀ τ, ∀ X ∈ lieAt S τ, ∀ g,
    HasDerivAt (fun t : ℝ => L (om (g * oneP θ S τ X t, 1) f)) (L (om (g, 1) (dOmS θ om τ X f))) 0

def Induced (R : (GA D S → ℂ) → (GA D S → ℂ)) : Prop :=
  ∀ f, IsThetaFunO ψ S T f → ∃ f', IsThetaFunO ψ S T f' ∧
    ∀ L, Adapted ψ om θ L → R (fun g => L (om (g, 1) f)) = fun g => L (om (g, 1) f')

variable {ψ om θ} {χS χT : (AE D)ˣ →* Circle}

theorem Induced.comp {R R' : (GA D S → ℂ) → (GA D S → ℂ)} (h : Induced ψ om θ R) (h' : Induced ψ om θ R') :
    Induced ψ om θ fun F => R (R' F) := fun f hf => by
  obtain ⟨f₁, h₁, e₁⟩ := h' f hf
  obtain ⟨f₂, h₂, e₂⟩ := h f₁ h₁
  exact ⟨f₂, h₂, fun L hL => by beta_reduce; rw [e₁ L hL, e₂ L hL]⟩

theorem Induced.smul (hω : IsWeilDatumO ψ S T χS χT om) (c : ℂ) {R : (GA D S → ℂ) → (GA D S → ℂ)}
    (h : Induced ψ om θ R) : Induced ψ om θ fun F => c • R F := fun f hf => by
  obtain ⟨f₁, h₁, e₁⟩ := h f hf
  refine ⟨c • f₁, GlobalTheory.OrientedHeis.theta_smul c h₁, fun L hL => ?_⟩
  beta_reduce
  rw [e₁ L hL]
  funext g
  rw [map_smul, hL.2.1 c _ (hω.om_pres _ _ h₁)]
  rfl

theorem Induced.add (hω : IsWeilDatumO ψ S T χS χT om) {R R' : (GA D S → ℂ) → (GA D S → ℂ)}
    (h : Induced ψ om θ R) (h' : Induced ψ om θ R') : Induced ψ om θ fun F => R F + R' F := fun f hf => by
  obtain ⟨f₁, h₁, e₁⟩ := h f hf
  obtain ⟨f₂, h₂, e₂⟩ := h' f hf
  refine ⟨f₁ + f₂, GlobalTheory.OrientedHeis.theta_add h₁ h₂, fun L hL => ?_⟩
  beta_reduce
  rw [e₁ L hL, e₂ L hL]
  funext g
  rw [map_add, hL.1 _ _ (hω.om_pres _ _ h₁) (hω.om_pres _ _ h₂)]
  rfl

section Mix

variable {S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ)

variable {μ : Measure (Mx D T.rank ρ)} {𝓕 : Set (Mx D T.rank ρ)}

end Mix

end GlobalTheory.Core.Rk.SchCen

end
