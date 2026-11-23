import Formalism.PeriodIntegrals.LatDefs

open Classical

namespace PI

def TransInvLat : Prop :=
  ∀ w₁ w₂ : ℂ, ((starRingEnd ℂ) w₁ * w₂).im ≠ 0 → ∀ G : ℂ → ℂ,
    (∀ ω ∈ lat2 w₁ w₂, ∀ z, U1 (lat2 w₁ w₂) ω G z = (if ω / 2 ∈ lat2 w₁ w₂ then 1 else -1) * G z) →
    ∀ (x ω : ℂ) (m : ℕ), 0 < m → (m : ℂ) * (x / 2) ∈ lat2 w₁ w₂ → ω ∈ lat2 w₁ w₂ →
      U1 (lat2 w₁ w₂) (x + 2 * (m : ℂ) * ω) G = U1 (lat2 w₁ w₂) x G

end PI
