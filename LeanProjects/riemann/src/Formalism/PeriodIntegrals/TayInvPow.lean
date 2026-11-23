import Mathlib

namespace PI

open MvPowerSeries

universe u v

def TayInvPow : Prop :=
  ∀ (σ : Type u) (A : Type v) [CommRing A] (τ : A →+* MvPowerSeries σ A) (s t : A) (c : σ →₀ A),
    s * t = 1 →
    τ s = C s + c.sum (fun p a => C a * X p) →
    ∀ (k : ℕ) (β : σ →₀ ℕ),
      coeff β (τ (t ^ k)) =
        (-1) ^ (β.sum fun _ n => n) * (((k + (β.sum fun _ n => n) - 1).choose (β.sum fun _ n => n) : ℕ) : A) *
          ((Nat.multinomial β.support β : ℕ) : A) * (β.prod fun p b => c p ^ b) * t ^ (k + β.sum fun _ n => n)

end PI
