import Formalism.PeriodIntegrals.IsLowUnitH

open MeasureTheory Matrix Finset
open scoped InnerProductSpace ComplexOrder ContDiff

noncomputable section

namespace PI

open PI.UpqRep

section

variable {k r : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def IsCWCont {Wp : Type*} [NormedAddCommGroup Wp]
    (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)) (B : H → Wp) : Prop :=
  ∃ (C : ℝ) (Ws : List (List (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ))),
    (∀ w ∈ Ws, ∀ X ∈ w, InLieHpk k r X) ∧
    ∀ v ∈ smoothVecs (k := k) (r := r) σ, ‖B v‖ ≤ C * (Ws.map fun w => ‖dsigW σ w v‖).sum

def thetaH (k r : ℕ) (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ :=
  -(Hpk k r * Xᴴ * Hpk k r)

def dsigC (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)) (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (v : H) : H :=
  dsig (k := k) (r := r) σ ((1 / 2 : ℂ) • (X + thetaH k r X)) v +
    Complex.I • dsig (k := k) (r := r) σ ((-(Complex.I / 2)) • (X - thetaH k r X)) v

end

def BesselDeriv : Prop :=
  ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H))
    (Wp : Type) [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] (B : H → Wp),
    IsDSHpk k r ε lam σ →
    (∀ v ∈ smoothVecs (k := k) (r := r) σ, ∀ w ∈ smoothVecs (k := k) (r := r) σ, B (v + w) = B v + B w) →
    (∀ (c : ℂ), ∀ v ∈ smoothVecs (k := k) (r := r) σ, B (c • v) = c • B v) →
    IsCWCont (k := k) (r := r) σ B →
    ∀ (Y : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (θ : ℝ), Y * Y * Y = 0 →
      (∀ t : ℝ, (1 + (t : ℂ) • Y + ((t : ℂ) ^ 2 / 2) • (Y * Y)) ∈ UH (Hpk k r)) →
      (∀ t : ℝ, ∀ v ∈ smoothVecs (k := k) (r := r) σ,
        B (σ (1 + (t : ℂ) • Y + ((t : ℂ) ^ 2 / 2) • (Y * Y)) v) = Complex.exp (((θ * t : ℝ) : ℂ) * Complex.I) • B v) →
      ∀ w ∈ smoothVecs (k := k) (r := r) σ, ∀ g ∈ UH (Hpk k r),
        (∀ i : Fin (2 * r + k + 1) × Fin (2 * r + k + 1),
          dsigC (k := k) (r := r) σ (Matrix.single i.1 i.2 1) w ∈ smoothVecs (k := k) (r := r) σ) ∧
        ((θ : ℂ) * Complex.I) • B (σ g w) =
          ∑ i : Fin (2 * r + k + 1) × Fin (2 * r + k + 1),
            (g⁻¹ * Y * g) i.1 i.2 • B (σ g (dsigC (k := k) (r := r) σ (Matrix.single i.1 i.2 1) w))

end PI
