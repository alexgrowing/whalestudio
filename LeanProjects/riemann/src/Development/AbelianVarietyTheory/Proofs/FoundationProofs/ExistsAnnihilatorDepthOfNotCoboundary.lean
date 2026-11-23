import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.SoDefs
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.LocCharAnn

theorem approx_candidate {K : Type} [NormedField K] {Γ : Type} (k a : Γ → K) {s₀ : Γ}
    (hk : k s₀ ≠ 1) {X : K} {ε : ℝ}
    (h0 : ‖a s₀ - (k s₀ * X - X)‖ ≤ ε) (s : Γ) (hs : ‖a s - (k s * X - X)‖ ≤ ε) :
    ‖a s - (k s * (a s₀ / (k s₀ - 1)) - a s₀ / (k s₀ - 1))‖ ≤
      (1 + ‖k s - 1‖ / ‖k s₀ - 1‖) * ε := by
  have hk' : k s₀ - 1 ≠ 0 := sub_ne_zero.mpr hk
  have hpos : 0 < ‖k s₀ - 1‖ := norm_pos_iff.mpr hk'
  set X₀ := a s₀ / (k s₀ - 1)
  have hX : X₀ - X = (a s₀ - (k s₀ * X - X)) / (k s₀ - 1) := by
    simp only [X₀]; field_simp
  have hXn : ‖X₀ - X‖ ≤ ε / ‖k s₀ - 1‖ := by
    rw [hX, norm_div]; exact div_le_div_of_nonneg_right h0 hpos.le
  have hid : a s - (k s * X₀ - X₀) = (a s - (k s * X - X)) - (k s - 1) * (X₀ - X) := by ring
  rw [hid]
  calc ‖(a s - (k s * X - X)) - (k s - 1) * (X₀ - X)‖
      ≤ ‖a s - (k s * X - X)‖ + ‖(k s - 1) * (X₀ - X)‖ := norm_sub_le _ _
    _ ≤ ε + ‖k s - 1‖ * (ε / ‖k s₀ - 1‖) := by
        rw [norm_mul]; gcongr
    _ = (1 + ‖k s - 1‖ / ‖k s₀ - 1‖) * ε := by field_simp

theorem exists_depth_of_not_coboundary : ∀ (l : ℕ) [Fact l.Prime] {Γ : Type} (H : Set Γ) (k a : Γ → Qbar l), (∃ s ∈ H, k s ≠ 1) → (¬ ∃ X : Qbar l, ∀ s ∈ H, a s = k s * X - X) → ∃ r : ℕ, ∀ (n : ℕ) (x y : Qbar l), ‖x‖ ≤ 1 → (∀ s ∈ H, ‖x * a s - (k s * y - y)‖ ≤ ‖((l : ℕ) : Qbar l) ^ n‖) → ‖x‖ ≤ ‖((l : ℕ) : Qbar l) ^ (n - r)‖ := by
  intro l _ Γ H k a ⟨s₀, hs₀, hk⟩ hna
  by_contra hcon
  push_neg at hcon
  set q : ℝ := ‖((l : ℕ) : Qbar l)‖ with hq
  have hq1 : q < 1 := GlobalTheory.CoefEmbed.norm_prime_lt_one
  have hq0 : 0 ≤ q := norm_nonneg _
  have happrox : ∀ r : ℕ, ∃ X : Qbar l, ∀ t ∈ H, ‖a t - (k t * X - X)‖ ≤ q ^ r := by
    intro r
    obtain ⟨n, x, y, hx1, hb, hx⟩ := hcon r
    rw [norm_pow] at hx hb
    by_cases hnr : n < r
    · rw [Nat.sub_eq_zero_of_le hnr.le, pow_zero] at hx
      exact absurd hx (not_lt.mpr hx1)
    push_neg at hnr
    have hxpos : 0 < ‖x‖ := lt_of_le_of_lt (pow_nonneg hq0 _) hx
    have hx0 : x ≠ 0 := norm_pos_iff.mp hxpos
    refine ⟨y / x, fun t ht => ?_⟩
    have hid : x * a t - (k t * y - y) = x * (a t - (k t * (y / x) - y / x)) := by
      field_simp
    have h1 := hb t ht
    rw [hid, norm_mul] at h1
    have hsplit : q ^ n = q ^ (n - r) * q ^ r := by
      rw [← pow_add, Nat.sub_add_cancel hnr]
    rw [hsplit] at h1
    by_contra hlt
    push_neg at hlt
    have : q ^ (n - r) * q ^ r < ‖x‖ * ‖a t - (k t * (y / x) - y / x)‖ :=
      mul_lt_mul'' hx hlt (pow_nonneg hq0 _) (pow_nonneg hq0 _)
    linarith
  apply hna
  refine ⟨a s₀ / (k s₀ - 1), fun s hs => ?_⟩
  set C : ℝ := 1 + ‖k s - 1‖ / ‖k s₀ - 1‖
  have hbound : ∀ r : ℕ, ‖a s - (k s * (a s₀ / (k s₀ - 1)) - a s₀ / (k s₀ - 1))‖ ≤ C * q ^ r := by
    intro r
    obtain ⟨X, hX⟩ := happrox r
    exact approx_candidate k a hk (hX s₀ hs₀) s (hX s hs)
  have hlim : Filter.Tendsto (fun r : ℕ => C * q ^ r) Filter.atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).const_mul C
  have hle := ge_of_tendsto' hlim hbound
  have h0 : ‖a s - (k s * (a s₀ / (k s₀ - 1)) - a s₀ / (k s₀ - 1))‖ = 0 :=
    le_antisymm hle (norm_nonneg _)
  exact sub_eq_zero.mp (norm_eq_zero.mp h0)

end GlobalTheory.LocCharAnn
