import Formalism.PeriodIntegrals.TransInvLat
import Formalism.PeriodIntegrals.AreaLat

open Classical Complex

namespace PI.TransInvLatW

theorem shift_core (P A : ℂ) (G : ℂ → ℂ) (x y X Y : ℂ)
    (hy : ∀ z, G (z + y) * exp (-P * z * Y / A - P * y * Y / (2 * A)) = G z)
    (hph : exp (P * (x * Y - y * X) / (2 * A)) = 1) (z : ℂ) :
    G (z + (x + y)) * exp (-P * z * (X + Y) / A - P * (x + y) * (X + Y) / (2 * A)) =
      G (z + x) * exp (-P * z * X / A - P * x * X / (2 * A)) := by
  have h1 := hy (z + x)
  have hz : z + (x + y) = z + x + y := by ring
  rw [hz, ← h1, mul_assoc (G (z + x + y)), ← Complex.exp_add]
  congr 1
  have hE : -P * z * (X + Y) / A - P * (x + y) * (X + Y) / (2 * A) =
      (-P * (z + x) * Y / A - P * y * Y / (2 * A) + (-P * z * X / A - P * x * X / (2 * A))) +
        P * (x * Y - y * X) / (2 * A) := by ring
  rw [hE, Complex.exp_add, hph, mul_one]

def PhaseOne : Prop :=
  ∀ w₁ w₂ : ℂ, ((starRingEnd ℂ) w₁ * w₂).im ≠ 0 → ∀ (x ω : ℂ) (m : ℕ), 0 < m →
    (m : ℂ) * (x / 2) ∈ lat2 w₁ w₂ → ω ∈ lat2 w₁ w₂ →
      exp ((Real.pi : ℂ) * (x * (starRingEnd ℂ) (2 * (m : ℂ) * ω) -
        (2 * (m : ℂ) * ω) * (starRingEnd ℂ) x) / (2 * (area (lat2 w₁ w₂) : ℂ))) = 1

theorem transInvLat_of_phase (h : PhaseOne) : PI.TransInvLat := by
  intro w₁ w₂ hD G hG x ω m hm hx hω
  have hy : 2 * (m : ℂ) * ω ∈ lat2 w₁ w₂ := by
    have : 2 * (m : ℂ) * ω = (2 * m : ℕ) • ω := by rw [nsmul_eq_mul]; push_cast; ring
    rw [this]; exact AddSubgroup.nsmul_mem _ hω _
  have hy2 : 2 * (m : ℂ) * ω / 2 ∈ lat2 w₁ w₂ := by
    have : 2 * (m : ℂ) * ω / 2 = m • ω := by rw [nsmul_eq_mul]; ring
    rw [this]; exact AddSubgroup.nsmul_mem _ hω _
  have hG' := hG _ hy
  simp only [if_pos hy2, one_mul] at hG'
  funext z
  unfold U1
  rw [map_add]
  exact shift_core _ _ G x _ _ _ (fun z => hG' z) (h w₁ w₂ hD x ω m hm hx hω) z

end PI.TransInvLatW
