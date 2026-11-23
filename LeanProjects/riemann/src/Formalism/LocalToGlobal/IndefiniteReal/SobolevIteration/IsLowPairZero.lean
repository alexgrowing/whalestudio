import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteReal.SobolevIteration.CuspOfLowVanish

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Mult
  MeasureTheory IsDedekindDomain NumberField

namespace Formalism.IndefR.Tow

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

open Classical in

def IsLowPair (θ : InfFam D) {S T' : HSp D} {Ss : D.what₂.Tau → SPar} (M : DSModel S Ss)
    (om' : GA D S × GA D T' →* Module.End ℂ (WO S T' → ℂ)) (pt' : MvPolynomial (FVar D T'.rank S.rank) ℂ → (WO S T' → ℂ))
    (B : MvPolynomial (FVar D T'.rank S.rank) ℂ → M.Vec → (GA D T' → ℂ)) : Prop :=
  (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D S τ), ∀ φ φ', pt' φ' = om' (atTau θ S τ g, 1) (pt' φ) →
    ∀ (v : M.Vec) (w : M.sm τ), (w : M.H τ) = M.rep τ g (v τ) → B φ' (Function.update v τ w) = B φ v) ∧
  (∀ τ, ∀ X ∈ lieAt S τ, ∀ φ φ', (∀ z, HasDerivAt (fun t : ℝ => om' (oneP θ S τ X t, 1) (pt' φ) z) (pt' φ' z) 0) →
    ∀ (v : M.Vec) (w : M.sm τ),
      HasDerivAt (fun t : ℝ => M.rep τ (NormedSpace.exp (t • X)) (v τ)) (w : M.H τ) 0 →
      B φ' v + B φ (Function.update v τ w) = 0) ∧
  (∀ τ, ∀ k ∈ Formalism.QuantumDeterminants.UH (gramAt D T' τ), ∀ φ φ', pt' φ' = om' (1, atTau θ T' τ k) (pt' φ) →
    ∀ v g', B φ' v g' = B φ v (g' * atTau θ T' τ k)) ∧
  (∀ τ, ∀ Y ∈ lieAt T' τ, ∀ φ φ', (∀ z, HasDerivAt (fun t : ℝ => om' (1, oneP θ T' τ Y t) (pt' φ) z) (pt' φ' z) 0) →
    ∀ v g', HasDerivAt (fun t : ℝ => B φ v (g' * oneP θ T' τ Y t)) (B φ' v g') 0)

def liftPair {S T' : HSp D} {Ss : D.what₂.Tau → SPar} (M : DSModel S Ss)
    (om' : GA D S × GA D T' →* Module.End ℂ (WO S T' → ℂ)) (pt' : MvPolynomial (FVar D T'.rank S.rank) ℂ → (WO S T' → ℂ))
    (ν : Measure (GA D S)) (𝓕 : Set (GA D S)) (T : MMap M) : MvPolynomial (FVar D T'.rank S.rank) ℂ → M.Vec → (GA D T' → ℂ) :=
  fun φ v => liftO om' ν 𝓕 (pt' φ) (T v)

def LowDom (θ : InfFam D) {S T' : HSp D} {Ss : D.what₂.Tau → SPar} (M : DSModel S Ss)
    (om' : GA D S × GA D T' →* Module.End ℂ (WO S T' → ℂ)) (pt' : MvPolynomial (FVar D T'.rank S.rank) ℂ → (WO S T' → ℂ))
    (ν : Measure (GA D S)) (𝓕 : Set (GA D S)) (T : MMap M) : Prop :=
  (∀ τ, ∀ X ∈ lieAt S τ, ∀ φ (v : M.Vec) (g' : GA D T'),
    (∀ t : ℝ, |t| < 1 → IntegrableOn (fun h => thetaKO om' (h * oneP θ S τ X t) g' (pt' φ) *
      T v (h * oneP θ S τ X t)) 𝓕 ν) ∧
    ∃ G : GA D S → ℝ, IntegrableOn G 𝓕 ν ∧ ∀ t : ℝ, |t| < 1 → ∀ h ∈ 𝓕,
      ‖deriv (fun s : ℝ => thetaKO om' (h * oneP θ S τ X s) g' (pt' φ) * T v (h * oneP θ S τ X s)) t‖ ≤ G h) ∧
  (∀ τ, ∀ Y ∈ lieAt T' τ, ∀ φ (v : M.Vec) (g' : GA D T'),
    (∀ t : ℝ, |t| < 1 → IntegrableOn (fun h => thetaKO om' h (g' * oneP θ T' τ Y t) (pt' φ) * T v h) 𝓕 ν) ∧
    ∃ G : GA D S → ℝ, IntegrableOn G 𝓕 ν ∧ ∀ t : ℝ, |t| < 1 → ∀ h ∈ 𝓕,
      ‖deriv (fun s : ℝ => thetaKO om' h (g' * oneP θ T' τ Y s) (pt' φ) * T v h) t‖ ≤ G h)

def LowKerDer (θ : InfFam D) {S T' : HSp D} (om' : GA D S × GA D T' →* Module.End ℂ (WO S T' → ℂ))
    (pt' : MvPolynomial (FVar D T'.rank S.rank) ℂ → (WO S T' → ℂ)) : Prop :=
  (∀ τ, ∀ X ∈ lieAt S τ, ∀ φ φ', (∀ z, HasDerivAt (fun t : ℝ => om' (oneP θ S τ X t, 1) (pt' φ) z) (pt' φ' z) 0) →
    ∀ h g', HasDerivAt (fun t : ℝ => thetaKO om' (h * oneP θ S τ X t) g' (pt' φ)) (thetaKO om' h g' (pt' φ')) 0) ∧
  (∀ τ, ∀ Y ∈ lieAt T' τ, ∀ φ φ', (∀ z, HasDerivAt (fun t : ℝ => om' (1, oneP θ T' τ Y t) (pt' φ) z) (pt' φ' z) 0) →
    ∀ h g', HasDerivAt (fun t : ℝ => thetaKO om' h (g' * oneP θ T' τ Y t) (pt' φ)) (thetaKO om' h g' (pt' φ')) 0)

def LowPairOfLift (D : D7) : Prop :=
  ∀ (θ : InfFam D), IsInfFam θ → ∀ (ψ : AddChar (AF D.host.F) ℂ) (S T' : HSp D) (χS χT : (AE D)ˣ →* Circle)
    {Ss : D.what₂.Tau → SPar} (M : DSModel S Ss) (J : Set (GA D S)) (χ : GA D S → ℂ) (T : MMap M),
    IsMultMap θ M J χ T →
    ∀ om' : GA D S × GA D T' →* Module.End ℂ (WO S T' → ℂ), IsWeilDatumO ψ S T' χS χT om' →
    ∀ pt' : MvPolynomial (FVar D T'.rank S.rank) ℂ → (WO S T' → ℂ), (∀ φ, IsThetaFunO ψ S T' (pt' φ)) →
    ∀ (ν : Measure (GA D S)) (𝓕 : Set (GA D S)), MeasurableSet 𝓕 →
      (∀ Φ : GA D S → ℂ, (∀ γ ∈ GQ S, ∀ h, Φ (γ * h) = Φ h) → ∀ k : GA D S,
        (IntegrableOn (fun h => Φ (h * k)) 𝓕 ν ↔ IntegrableOn Φ 𝓕 ν) ∧ ∫ h in 𝓕, Φ (h * k) ∂ν = ∫ h in 𝓕, Φ h ∂ν) →
      LowKerDer θ om' pt' → LowDom θ M om' pt' ν 𝓕 T →
      IsLowPair θ M om' pt' (liftPair M om' pt' ν 𝓕 T)

end Formalism.IndefR.Tow

end
