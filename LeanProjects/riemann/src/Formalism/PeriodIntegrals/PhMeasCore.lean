import Mathlib

open MeasureTheory Matrix
open scoped InnerProductSpace ContDiff

noncomputable section

namespace PI

namespace PhMeasCore

variable {n : ℕ}

def Jm (ε : Fin n → Bool) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.diagonal fun a => if ε a then 1 else -1

def UJset (ε : Fin n → Bool) : Set (Matrix (Fin n) (Fin n) ℂ) := {g | gᴴ * Jm ε * g = Jm ε}

def UH (Hm : Matrix (Fin n) (Fin n) ℂ) : Set (Matrix (Fin n) (Fin n) ℂ) := {g | gᴴ * Hm * g = Hm}

section Smooth

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def SmoothOnH {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (Hm : Matrix (Fin n) (Fin n) ℂ)
    (f : Matrix (Fin n) (Fin n) ℂ → E) : Prop :=
  ∀ g₀, g₀ᴴ * Hm * g₀ = Hm → ∃ (U : Set (Matrix (Fin n) (Fin n) ℂ)) (F : Matrix (Fin n) (Fin n) ℂ → E),
    IsOpen U ∧ g₀ ∈ U ∧ ContDiffOn ℝ ∞ F U ∧ ∀ g ∈ U, g ∈ UH Hm → f g = F g

end Smooth

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def smoothVecs (Hm : Matrix (Fin n) (Fin n) ℂ) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Set H :=
  {v | SmoothOnH Hm (fun g => σ g v)}

def InLie (Hm X : Matrix (Fin n) (Fin n) ℂ) : Prop := Xᴴ * Hm + Hm * X = 0

def dsig (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (X : Matrix (Fin n) (Fin n) ℂ) (v : H) : H :=
  deriv (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) v) 0

def dsigW (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : List (Matrix (Fin n) (Fin n) ℂ) → H → H
  | [], v => v
  | X :: w, v => dsig σ X (dsigW σ w v)

def IsCWCont {Wp : Type*} [NormedAddCommGroup Wp] (Hm : Matrix (Fin n) (Fin n) ℂ)
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (B : H → Wp) : Prop :=
  ∃ (C : ℝ) (Ws : List (List (Matrix (Fin n) (Fin n) ℂ))),
    (∀ w ∈ Ws, ∀ X ∈ w, InLie Hm X) ∧
    ∀ v ∈ smoothVecs Hm σ, ‖B v‖ ≤ C * (Ws.map fun w => ‖dsigW σ w v‖).sum

end PhMeasCore

open PhMeasCore in

def PhMeasCore : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (Hm : Matrix (Fin n) (Fin n) ℂ) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (Wp : Type) [NormedAddCommGroup Wp] [NormedSpace ℂ Wp]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (B : H → Wp) (w : H),
    (∃ P : Matrix (Fin n) (Fin n) ℂ, IsUnit P ∧ Pᴴ * Jm ε * P = Hm ∧
      (σ (P⁻¹ * 1 * P) = 1 ∧ ∀ a ∈ UJset ε, ∀ b ∈ UJset ε, σ (P⁻¹ * (a * b) * P) = (σ (P⁻¹ * a * P)).comp (σ (P⁻¹ * b * P))) ∧
      ∀ v : H, ContinuousOn (fun g => σ (P⁻¹ * g * P) v) (UJset ε)) →
    (∀ v ∈ smoothVecs Hm σ, ∀ v' ∈ smoothVecs Hm σ, B (v + v') = B v + B v') →
    (∀ c : ℂ, ∀ v ∈ smoothVecs Hm σ, B (c • v) = c • B v) →
    IsCWCont Hm σ B →
    w ∈ smoothVecs Hm σ →
    Measurable (Set.indicator {x : Fin n → Fin n → ℂ | Matrix.of x ∈ UH Hm} (fun x => ‖B (σ (Matrix.of x) w)‖))

end PI

end
