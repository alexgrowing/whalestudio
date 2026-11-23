import Mathlib

open Filter Topology
open scoped ContDiff

noncomputable section

namespace SmoothVectors

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def IsClosedMatrixGroup (G : Set (Matrix (Fin n) (Fin n) ℂ)) : Prop :=
  IsClosed G ∧ (1 : Matrix (Fin n) (Fin n) ℂ) ∈ G ∧ (∀ g ∈ G, ∀ h ∈ G, g * h ∈ G) ∧
    ∀ g ∈ G, ∃ h ∈ G, h * g = 1 ∧ g * h = 1

def IsIsomRep (G : Set (Matrix (Fin n) (Fin n) ℂ)) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Prop :=
  (∀ g ∈ G, ∀ h ∈ G, σ (g * h) = (σ g).comp (σ h)) ∧ (∀ g ∈ G, ∀ v : H, ‖σ g v‖ = ‖v‖) ∧
    ∀ v : H, ContinuousOn (fun g => σ g v) G

def lieAlg (G : Set (Matrix (Fin n) (Fin n) ℂ)) : Set (Matrix (Fin n) (Fin n) ℂ) :=
  {X | ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • X) ∈ G}

def SmoothOn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (G : Set (Matrix (Fin n) (Fin n) ℂ))
    (f : Matrix (Fin n) (Fin n) ℂ → E) : Prop :=
  ∀ g₀ ∈ G, ∃ (U : Set (Matrix (Fin n) (Fin n) ℂ)) (F : Matrix (Fin n) (Fin n) ℂ → E),
    IsOpen U ∧ g₀ ∈ U ∧ ContDiffOn ℝ ∞ F U ∧ ∀ g ∈ U, g ∈ G → f g = F g

def smoothVecs (G : Set (Matrix (Fin n) (Fin n) ℂ)) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Set H :=
  {v | SmoothOn G (fun g => σ g v)}

def dsig (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (X : Matrix (Fin n) (Fin n) ℂ) (v : H) : H :=
  deriv (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) v) 0

def dsigW (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : List (Matrix (Fin n) (Fin n) ℂ) → H → H
  | [], v => v
  | X :: w, v => dsig σ X (dsigW σ w v)

def SmComplete : Prop :=
  ∀ (n : ℕ) (G : Set (Matrix (Fin n) (Fin n) ℂ)) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)),
    IsClosedMatrixGroup G → IsIsomRep G σ →
    ∀ v : ℕ → H, (∀ m, v m ∈ smoothVecs G σ) →
      (∀ w : List (Matrix (Fin n) (Fin n) ℂ), (∀ X ∈ w, X ∈ lieAlg G) →
        CauchySeq fun m => dsigW σ w (v m)) →
      ∃ v₀ ∈ smoothVecs G σ, ∀ w : List (Matrix (Fin n) (Fin n) ℂ), (∀ X ∈ w, X ∈ lieAlg G) →
        Tendsto (fun m => dsigW σ w (v m)) atTop (𝓝 (dsigW σ w v₀))

end SmoothVectors

end
