import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HasDerivAtDOmT
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchrodingerFunctionUnitaryLeviRadicalActions
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitLocalPlaceLocalModelsLinearSubspace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumThetaJointlyContinuous
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOneP
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

namespace GlobalTheory.Core.Rk.SchCentre

open GlobalTheory.Core.Rk.SWLaw

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {A B : HSp D} {χ : (AE D)ˣ →* Circle}
  {om : GA D (dblSp A) × GA D B →* Module.End ℂ (WO (dblSp A) B → ℂ)} {ν : Measure (WO A B)} {𝓨 : Set (WO A B)}

def Lifts (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D)
    (om : GA D (dblSp A) × GA D B →* Module.End ℂ (WO (dblSp A) B → ℂ)) (ν : Measure (WO A B)) (𝓨 : Set (WO A B))
    (O : (GA D B → ℂ) → GA D B → ℂ) : Prop :=
  ∃ L : (WO (dblSp A) B → ℂ) → WO (dblSp A) B → ℂ,
    (∀ f, IsThetaFunO ψ (dblSp A) B f → IsThetaFunO ψ (dblSp A) B (L f)) ∧
    (∀ f, IsThetaFunO ψ (dblSp A) B f → ∀ w, O (fun h => om (1, h) f w) = fun h => om (1, h) (L f) w) ∧
    (∀ f, IsThetaFunO ψ (dblSp A) B f → ∀ x,
      O (fun h => sch ψ A B ν 𝓨 (om (1, h) f) x) = fun h => sch ψ A B ν 𝓨 (om (1, h) (L f)) x)

section Closure

variable (hW : IsWeilDatumO ψ (dblSp A) B 1 χ om) (hν : IsCovolOne (ratL B A) ν 𝓨)
include hW hν

end Closure

section Mix

open GlobalTheory.IndefiniteRowSideFullHecke.RapidDecayLift (dOmT)

variable {S T S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {χS χT : (AE D)ˣ →* Circle} {θ : InfFam D}
  {ω : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}

end Mix

end GlobalTheory.Core.Rk.SchCentre

end
