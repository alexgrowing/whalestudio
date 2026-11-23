import Formalism.LocalToGlobal.BesselHermitianTheta.TiedSmooth
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory Matrix
open scoped TensorProduct ContDiff

namespace Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Rep

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  (Lie : Set (Matrix (Fin n) (Fin n) ℂ)) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H))

def SmoothVec (w : H) : Prop :=
  ∀ (k : ℕ) (Xs : Fin k → Matrix (Fin n) (Fin n) ℂ), (∀ i, Xs i ∈ Lie) →
    ContDiff ℝ ∞ fun t : Fin k → ℝ => σ ((List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod) w

def dRep (X : Matrix (Fin n) (Fin n) ℂ) (w : H) : H := deriv (fun t : ℝ => σ (NormedSpace.exp (t • X)) w) 0

def Sobolev₂ (ℓ : H →ₗ[ℂ] ℂ) : Prop :=
  ∃ (S : List (List (Matrix (Fin n) (Fin n) ℂ))) (C : ℝ), (∀ l ∈ S, ∀ X ∈ l, X ∈ Lie) ∧
    ∀ w, SmoothVec Lie σ w → ‖ℓ w‖ ≤ C * (S.map fun l => ‖l.foldr (dRep σ) w‖).sum

end Rep

variable {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D)

def IsTypeAt (τ : D.what₂.Tau) (S : SPar) (φ : GA D V → ℂ) : Prop :=
  ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
    (σ : Matrix (Fin V.rank) (Fin V.rank) ℂ → (H →L[ℂ] H)) (lam : Fin V.rank → ℝ) (ε : Fin V.rank → Bool)
    (P : Matrix (Fin V.rank) (Fin V.rank) ℂ),
    IsEnum S lam ε ∧ IsDS ε lam σ ∧ IsUnit P ∧ Pᴴ * Formalism.REAL.Jm ε * P = gramAt D V τ ∧
    ∀ x, ∃ v : ℕ → H, (∀ i, SmoothVec (lieAt V τ) (fun g => σ (P * g * P⁻¹)) (v i)) ∧
      ∃ ℓ : ℕ → (H →ₗ[ℂ] ℂ), (∀ i, Sobolev₂ (lieAt V τ) (fun g => σ (P * g * P⁻¹)) (ℓ i)) ∧

        (∃ (S : List (List (Matrix (Fin V.rank) (Fin V.rank) ℂ))) (C : ℕ → ℝ), (∀ l ∈ S, ∀ X ∈ l, X ∈ lieAt V τ) ∧
          (∀ i w, SmoothVec (lieAt V τ) (fun g => σ (P * g * P⁻¹)) w →
            ‖ℓ i w‖ ≤ C i * (S.map fun l => ‖l.foldr (dRep (fun g => σ (P * g * P⁻¹))) w‖).sum) ∧
          (∀ S' : List (List (Matrix (Fin V.rank) (Fin V.rank) ℂ)), (∀ l ∈ S', ∀ X ∈ l, X ∈ lieAt V τ) →
            Summable (fun i => C i * (S'.map fun l => ‖l.foldr (dRep (fun g => σ (P * g * P⁻¹))) (v i)‖).sum)) ∧

          (∃ B : Matrix (Fin V.rank) (Fin V.rank) ℂ → ℝ, Continuous B ∧ ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ w,
            SmoothVec (lieAt V τ) (fun g => σ (P * g * P⁻¹)) w →
            (S.map fun l => ‖l.foldr (dRep (fun g => σ (P * g * P⁻¹))) (σ (P * g * P⁻¹) w)‖).sum ≤
              B g * (S.map fun l => ‖l.foldr (dRep (fun g => σ (P * g * P⁻¹))) w‖).sum)) ∧
        ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), HasSum (fun i => ℓ i (σ (P * g * P⁻¹) (v i))) (φ (x * atTau θ V τ g))

def TypTied {X : ThetaX D} (T : ThetaTied D X) : Prop :=
  AllSome (IsInfFam (D := D)) fun θ => ∀ V : HSp D, V.SigOK → ∀ P : D.what₂.Tau → SPar,
    (∀ τ, GoodPar V.rank (V.sig (tauE D τ)).1 (V.sig (tauE D τ)).2 (P τ)) →
    (∀ τ, SParGap V.rank (V.sig (tauE D τ)).1 (V.sig (tauE D τ)).2 (P τ)) →
    ∀ F, F ∈ X.typ V P ↔ ∀ τ, IsTypeAt θ V τ (P τ) (T.ev V F)

end Formalism.L2.Theta

end
