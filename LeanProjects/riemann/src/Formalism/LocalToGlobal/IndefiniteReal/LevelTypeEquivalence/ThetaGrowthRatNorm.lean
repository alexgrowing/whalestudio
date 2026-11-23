import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.ThetaSquareIntegrable
import Formalism.LocalToGlobal.BesselHermitianTheta.TiedSmooth

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
  IsDedekindDomain NumberField
open scoped TensorProduct

namespace Formalism.IndefR.Eqv

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def ThetaGrowthNorm (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om →
    ∀ θ : InfFam D, IsInfFam θ → Nonempty D.what₂.Tau → 0 < S.rank → 0 < T.rank →
      ∀ f, IsThetaFunO ψ S T f → ∀ K : Set (GA D S × GA D T), IsCompact K →
        ∃ (N : ℕ) (C : ℝ), ∀ k ∈ K, ∀ a ∈ GinfC S, ∀ b ∈ GinfC T,
          ‖thetaKO om (a * k.1) (b * k.2) f‖ ≤ C * (normInf θ S a * normInf θ T b) ^ N

def ThetaGrowthRatNorm (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om →
    ∀ θ : InfFam D, IsInfFam θ → Nonempty D.what₂.Tau → 0 < S.rank →
      ∀ f, IsThetaFunO ψ S T f → ∀ (K : Set (GA D S)) (K' : Set (GA D T)), IsCompact K → IsCompact K' →
        ∃ (N : ℕ) (C : ℝ), ∀ k ∈ K, ∀ a ∈ GinfC S, ∀ γ ∈ GQ T, ∀ c ∈ K',
          ‖thetaKO om (a * k) (γ * c) f‖ ≤ C * normInf θ S a ^ N

def ThetaModGrowthL (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om →
    ∀ θ : InfFam D, IsInfFam θ → Nonempty D.what₂.Tau → 0 < S.rank →
      ∀ f, IsThetaFunO ψ S T f → ∀ (h : GA D T) (x : GA D S), ∃ (C : ℝ) (N : ℕ), ∀ g ∈ GinfC S,
        ‖thetaKO om (x * g) h f‖ ≤ C * normInf θ S g ^ N

def ThetaModGrowthR (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om →
    ∀ θ : InfFam D, IsInfFam θ → Nonempty D.what₂.Tau → 0 < T.rank →
      ∀ f, IsThetaFunO ψ S T f → ∀ (g : GA D S) (x : GA D T), ∃ (C : ℝ) (N : ℕ), ∀ h ∈ GinfC T,
        ‖thetaKO om g (x * h) f‖ ≤ C * normInf θ T h ^ N

def DefCocompact (T : HSp D) : Prop :=
  ∃ K' : Set (GA D T), IsCompact K' ∧ ∀ h : GA D T, ∃ γ ∈ GQ T, ∃ k ∈ K', h = γ * k

def DefCocompactAll (D : D7) : Prop :=
  ∀ T : HSp D, Formalism.UG.IsTotDef D.sp.cm.sig T.gram → DefCocompact T

def ThetaGrowthDef (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om →
    ∀ θ : InfFam D, IsInfFam θ → Nonempty D.what₂.Tau → 0 < S.rank → DefCocompact T →
      ∀ f, IsThetaFunO ψ S T f → ∀ K : Set (GA D S), IsCompact K →
        ∃ (N : ℕ) (C : ℝ), ∀ k ∈ K, ∀ a ∈ GinfC S, ∀ h : GA D T,
          ‖thetaKO om (a * k) h f‖ ≤ C * normInf θ S a ^ N

end Formalism.IndefR.Eqv

end
