import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.LocalToGlobal.BesselHermitianTheta.TiedSmooth

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open scoped ContDiff

namespace GlobalTheory.IndefiniteRowSideFullHecke.RealSmoothQuadratic

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

abbrev HomC (S T : HSp D) : Type := Matrix (Fin T.rank) (Fin S.rank) ℂ

def dRhoO (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (τ : D.what₂.Tau) (z : HomC S T)
    (f : WO S T → ℂ) : WO S T → ℂ :=
  dRho (heisO ψ S T) θ τ z f

def quadSym (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (τ : D.what₂.Tau) {k : ℕ}
    (a : Fin k → ℂ) (z z' : Fin k → HomC S T) (f : WO S T → ℂ) : WO S T → ℂ :=
  fun w => ∑ i, a i * ((dRhoO ψ θ S T τ (z i) (dRhoO ψ θ S T τ (z' i) f) w +
    dRhoO ψ θ S T τ (z' i) (dRhoO ψ θ S T τ (z i) f) w) / 2)

def IsQuadOf (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (τ : D.what₂.Tau)
    (A : HomC S T → HomC S T) {k : ℕ} (a : Fin k → ℂ) (z z' : Fin k → HomC S T) : Prop :=
  ∀ (u : HomC S T) (f : WO S T → ℂ), IsThetaFunO ψ S T f →
    quadSym ψ θ S T τ a z z' (dRhoO ψ θ S T τ u f) - dRhoO ψ θ S T τ u (quadSym ψ θ S T τ a z z' f) =
      dRhoO ψ θ S T τ (A u) f

def HasQuadGen (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (τ : D.what₂.Tau)
    (A : HomC S T → HomC S T) (U : ℝ → Module.End ℂ (WO S T → ℂ)) : Prop :=
  ∃ (c : ℂ) (k : ℕ) (a : Fin k → ℂ) (z z' : Fin k → HomC S T), IsQuadOf ψ θ S T τ A a z z' ∧
    ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f → ∀ w : WO S T,
      HasDerivAt (fun t : ℝ => U t f w) (c * f w + quadSym ψ θ S T τ a z z' f w) 0

def prodOneP (θ : InfFam D) (V : HSp D) {k : ℕ} (τs : Fin k → D.what₂.Tau)
    (Xs : Fin k → Matrix (Fin V.rank) (Fin V.rank) ℂ) (t : Fin k → ℝ) : GA D V :=
  (List.ofFn fun i => oneP θ V (τs i) (Xs i) (t i)).prod

structure RealSmoothQuad (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) : Prop where

  genT : ∀ τ, ∀ X ∈ lieAt T τ, HasQuadGen ψ θ S T τ (fun u => X * u) fun t => om (1, oneP θ T τ X t)

  genS : ∀ τ, ∀ X ∈ lieAt S τ, HasQuadGen ψ θ S T τ (fun u => -(u * X)) fun t => om (oneP θ S τ X t, 1)

  smoothT : ∀ (k : ℕ) (τs : Fin k → D.what₂.Tau) (Xs : Fin k → Matrix (Fin T.rank) (Fin T.rank) ℂ),
    (∀ i, Xs i ∈ lieAt T (τs i)) → ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f → ∀ w : WO S T,
      ContDiff ℝ ∞ fun t : Fin k → ℝ => om (1, prodOneP θ T τs Xs t) f w

  smoothS : ∀ (k : ℕ) (τs : Fin k → D.what₂.Tau) (Xs : Fin k → Matrix (Fin S.rank) (Fin S.rank) ℂ),
    (∀ i, Xs i ∈ lieAt S (τs i)) → ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f → ∀ w : WO S T,
      ContDiff ℝ ∞ fun t : Fin k → ℝ => om (prodOneP θ S τs Xs t, 1) f w

def WeilRealGenerator (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om →
    ∀ θ : InfFam D, IsInfFam θ → RealSmoothQuad ψ θ S T om

end GlobalTheory.IndefiniteRowSideFullHecke.RealSmoothQuadratic

end
