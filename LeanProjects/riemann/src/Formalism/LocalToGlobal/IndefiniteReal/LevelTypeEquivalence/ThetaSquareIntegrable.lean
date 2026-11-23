import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
  IsDedekindDomain NumberField
open scoped TensorProduct ContDiff

namespace Formalism.IndefR.Eqv

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def ipO {S T : HSp D} (μ : Measure (WO S T)) (𝓕 : Set (WO S T)) (f f' : WO S T → ℂ) : ℂ :=
  ∫ w in 𝓕, f w * starRingEnd ℂ (f' w) ∂μ

def ThetaSquareIntegrable (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D), (∀ x, ‖ψ x‖ = 1) →
    ∀ f, IsThetaFunO ψ S T f → ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), μ.IsAddHaarMeasure →
      IsAddFundamentalDomain (ratL T S) 𝓕 μ → MemLp f 2 (μ.restrict 𝓕)

def IpUnit (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om →
    ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratL T S) 𝓕 μ →
      ∀ p f f', IsThetaFunO ψ S T f → IsThetaFunO ψ S T f' → ipO μ 𝓕 (om p f) (om p f') = ipO μ 𝓕 f f'

def CoefBound (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om →
    ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratL T S) 𝓕 μ →
      ∀ p f f', IsThetaFunO ψ S T f → IsThetaFunO ψ S T f' →
        ‖ipO μ 𝓕 (om p f) f'‖ ≤ Real.sqrt (nrm2 μ 𝓕 f) * Real.sqrt (nrm2 μ 𝓕 f')

def CoefCont (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om →
    FirstCountableTopology (GA D S) → FirstCountableTopology (GA D T) →
    ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratL T S) 𝓕 μ →
      ∀ f f', IsThetaFunO ψ S T f → IsThetaFunO ψ S T f' → Continuous fun p => ipO μ 𝓕 (om p f) f'

def IsRealFrame {S T : HSp D} {k : ℕ} (L : (Fin k → ℝ) →+ WO S T) : Prop :=
  Continuous L ∧ (∀ t, (L t).map (finPart D) = 0) ∧ ∀ w : WO S T, w.map (finPart D) = 0 → ∃ t, L t = w

def dH (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} {k n : ℕ} (L : (Fin k → ℝ) →+ WO S T) (l : Fin n → Fin k)
    (f : WO S T → ℂ) (w : WO S T) : ℂ :=
  iteratedFDeriv ℝ n (fun t : Fin k → ℝ => heisO ψ S T (L t) f w) 0 (fun i => Pi.single (l i) 1)

def sobO (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} {k : ℕ} (L : (Fin k → ℝ) →+ WO S T) (N : ℕ)
    (μ : Measure (WO S T)) (𝓕 : Set (WO S T)) (f : WO S T → ℂ) : ℝ :=
  ∑ n ∈ Finset.range (N + 1), ∑ l : Fin n → Fin k, Real.sqrt (∫ w in 𝓕, ‖dH ψ L l f w‖ ^ 2 ∂μ)

def ThetaSob (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D), IsStdChar D ψ (-1) →
    ∃ (k : ℕ) (L : (Fin k → ℝ) →+ WO S T) (N : ℕ), IsRealFrame L ∧
      ∀ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) →
        ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratL T S) 𝓕 μ →
          ∃ C : ℝ, ∀ f, IsThetaFunO ψ S T f → (∀ u ∈ U, u.map (infPart D) = 0 → heisO ψ S T u f = f) →
            ∀ w, ‖f w‖ ≤ C * sobO ψ L N μ 𝓕 f

def IsHgtInf (θ : InfFam D) (V : HSp D) (hgt : GA D V → ℝ) : Prop :=
  ∀ a ∈ GinfC V, 1 ≤ hgt a ∧ ∀ τ i j, ‖θ τ (infPart D (mt V a i j))‖ ≤ hgt a ∧ ‖θ τ (infPart D (mt V a⁻¹ i j))‖ ≤ hgt a

def ThetaGrowth (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om →
    ∀ θ : InfFam D, IsInfFam θ → ∀ (hS : GA D S → ℝ) (hT : GA D T → ℝ), IsHgtInf θ S hS → IsHgtInf θ T hT →
      ∀ f, IsThetaFunO ψ S T f → ∀ K : Set (GA D S × GA D T), IsCompact K →
        ∃ (N : ℕ) (C : ℝ), ∀ k ∈ K, ∀ a ∈ GinfC S, ∀ b ∈ GinfC T,
          ‖thetaKO om (a * k.1) (b * k.2) f‖ ≤ C * (hS a * hT b) ^ N

def ThetaGrowthRat (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om →
    ∀ θ : InfFam D, IsInfFam θ → ∀ hS : GA D S → ℝ, IsHgtInf θ S hS →
      ∀ f, IsThetaFunO ψ S T f → ∀ (K : Set (GA D S)) (K' : Set (GA D T)), IsCompact K → IsCompact K' →
        ∃ (N : ℕ) (C : ℝ), ∀ k ∈ K, ∀ a ∈ GinfC S, ∀ γ ∈ GQ T, ∀ c ∈ K',
          ‖thetaKO om (a * k) (γ * c) f‖ ≤ C * hS a ^ N

end Formalism.IndefR.Eqv

end
