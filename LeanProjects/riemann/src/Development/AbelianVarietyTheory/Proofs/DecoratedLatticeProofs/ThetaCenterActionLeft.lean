import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MeanPair
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.RegularisingElement
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.EisensteinResidue
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.FirstTermIdentitySchrodinger
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.EisensteinMaximalParabolic
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelEisensteinPolesStd
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelEisensteinSimplePoleOfDoublingMethod
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DifferentiableOneP
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HasDerivAtDOmT
open scoped Matrix NNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Rk.CenS

variable {D : D7} {S T : HSp D}

def Carried (ψ : AddChar (AF D.host.F) ℂ) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ))
    (A : (GA D S → ℂ) → (GA D S → ℂ)) : Prop :=
  ∀ f, IsThetaFunO ψ S T f → ∃ f', IsThetaFunO ψ S T f' ∧ ∀ w, A (fun g => om (g, 1) f w) = fun g => om (g, 1) f' w

variable {ψ : AddChar (AF D.host.F) ℂ} {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}

theorem Carried.comp {A B : (GA D S → ℂ) → (GA D S → ℂ)} (hA : Carried ψ om A) (hB : Carried ψ om B) :
    Carried ψ om fun φ => A (B φ) := fun f hf => by
  obtain ⟨f₁, hf₁, e₁⟩ := hB f hf
  obtain ⟨f₂, hf₂, e₂⟩ := hA f₁ hf₁
  exact ⟨f₂, hf₂, fun w => by simp only [e₁ w, e₂ w]⟩

theorem Carried.smul {A : (GA D S → ℂ) → (GA D S → ℂ)} (hA : Carried ψ om A) (c : ℂ) :
    Carried ψ om fun φ => c • A φ := fun f hf => by
  obtain ⟨f₁, hf₁, e₁⟩ := hA f hf
  refine ⟨c • f₁, (GlobalTheory.RealWeil.thetaSub ψ S T).smul_mem c hf₁, fun w => funext fun g => ?_⟩
  simp only [e₁ w, Pi.smul_apply, map_smul]

variable {θ : InfFam D} {χS χT : (AE D)ˣ →* Circle}

end GlobalTheory.Core.Rk.CenS

end
