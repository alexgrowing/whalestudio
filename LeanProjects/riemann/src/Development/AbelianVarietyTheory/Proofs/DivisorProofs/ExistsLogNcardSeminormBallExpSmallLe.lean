import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CharZeroFunctionField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EncardSeminormBallPowLeRadiusChangeStatement

set_option autoImplicit false

open Filter Topology GlobalTheory.VolBr

namespace GlobalTheory.VolBr

theorem log_ncard_ball_exp_le : ∀ (G : Type) [AddCommGroup G] (Λ : ℕ → AddSubgroup G) (B : ℕ → ℝ → Set G) (d : ℕ),
    0 < d → (∀ m, IsBallFam (Λ m) (B m)) → (∀ m R, (B m R).Finite) → ∀ C : ℝ,
    (∀ᶠ m : ℕ in atTop, Real.log ((B m (Real.exp (3 * m))).ncard : ℝ) ≤ C * (m : ℝ) ^ d) →
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ m : ℕ in atTop,
      Real.log ((B m (Real.exp (δ * m))).ncard : ℝ) ≤ Real.log ((B m 1).ncard : ℝ) + ε * (m : ℝ) ^ d := by
  intro G _ Λ B d _ hB hfin C hC ε hε
  set e : ℕ := max 1 ⌈C / ε⌉₊ with he_def
  have he1 : 1 ≤ e := le_max_left _ _
  have heR : (0 : ℝ) < e := by exact_mod_cast he1
  have he1R : (1 : ℝ) ≤ e := by exact_mod_cast he1
  have hCe : C ≤ ε * e := by
    have h1 : C / ε ≤ (⌈C / ε⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (⌈C / ε⌉₊ : ℝ) ≤ e := by exact_mod_cast le_max_right _ _
    rw [div_le_iff₀ hε] at h1
    nlinarith
  refine ⟨1 / e, by positivity, ?_⟩
  filter_upwards [hC, eventually_ge_atTop (3 * e)] with m hm hm3
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  set R := Real.exp (1 / e * m) with hR
  have hR1 : 1 ≤ R := Real.one_le_exp (by positivity)
  set Q := ⌈2 * R + 1⌉₊ with hQdef
  have hQ : 2 * R + 1 ≤ Q := Nat.le_ceil _
  have hQ4 : (Q : ℝ) ≤ 4 * R := by
    have := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ 2 * R + 1 by linarith)
    linarith
  have key := GlobalTheory.T.encard_seminormBall_pow_le_radius_change G (Λ m) (B m) (hB m) R Q e hR1 hQ (hfin m R)
  have mono : ∀ r s : ℝ, r ≤ s → B m r ⊆ B m s := by
    intro r s hrs x hx
    have := (hB m).sub_mem r (s - r) x 0 hx ((hB m).zero_mem _ (by linarith))
    simpa using this
  have hRe : R ^ (e + 1) ≤ Real.exp (2 * m) := by
    rw [hR, ← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    have : (m : ℝ) / e ≤ m := div_le_self hm0 he1R
    have h3 : ((e + 1 : ℕ) : ℝ) * (1 / e * m) = m + m / e := by
      push_cast; field_simp
    rw [h3]; linarith
  have hbig : R * (Q : ℝ) ^ e ≤ Real.exp (3 * m) := by
    have h4 : (4 : ℝ) ≤ Real.exp 3 := by
      have := Real.add_one_le_exp 3; linarith
    have hQ0 : (0 : ℝ) ≤ Q := Nat.cast_nonneg _
    calc R * (Q : ℝ) ^ e ≤ R * (4 * R) ^ e := by gcongr
      _ = 4 ^ e * R ^ (e + 1) := by ring
      _ ≤ Real.exp 3 ^ e * Real.exp (2 * m) := by gcongr
      _ = Real.exp (3 * e + 2 * m) := by rw [← Real.exp_nat_mul, ← Real.exp_add]; ring_nf
      _ ≤ Real.exp (3 * m) := by
        apply Real.exp_le_exp.mpr
        have : (3 * e : ℝ) ≤ m := by exact_mod_cast hm3
        linarith
  have hsub := mono _ _ hbig
  have hN : (B m R).ncard ^ e ≤ (B m 1).ncard ^ e * (B m (Real.exp (3 * m))).ncard := by
    rw [← (hfin m R).cast_ncard_eq, ← (hfin m 1).cast_ncard_eq, ← (hfin m _).cast_ncard_eq] at key
    norm_cast at key
    have hsub' : B m (R * ((Q ^ e : ℕ) : ℝ)) ⊆ B m (Real.exp (3 * m)) := by push_cast; exact hsub
    exact key.trans (Nat.mul_le_mul_left _ (Set.ncard_le_ncard hsub' (hfin m _)))
  have pos : ∀ r : ℝ, 0 ≤ r → (0 : ℝ) < (B m r).ncard := fun r hr => by
    exact_mod_cast (Set.ncard_pos (hfin m r)).mpr ⟨0, (hB m).zero_mem r hr⟩
  have hA := pos R (by linarith)
  have h1 := pos 1 zero_le_one
  have h3 := pos (Real.exp (3 * m)) (Real.exp_pos _).le
  have hNR : ((B m R).ncard : ℝ) ^ e ≤ ((B m 1).ncard : ℝ) ^ e * (B m (Real.exp (3 * m))).ncard := by
    exact_mod_cast hN
  have hlog := Real.log_le_log (by positivity) hNR
  rw [Real.log_mul (by positivity) h3.ne', Real.log_pow, Real.log_pow] at hlog
  have hCm : C * (m : ℝ) ^ d ≤ ε * e * (m : ℝ) ^ d := mul_le_mul_of_nonneg_right hCe (pow_nonneg hm0 d)
  have : (e : ℝ) * Real.log ((B m R).ncard : ℝ) ≤
      e * (Real.log ((B m 1).ncard : ℝ) + ε * (m : ℝ) ^ d) := by nlinarith
  exact le_of_mul_le_mul_left this heR

end GlobalTheory.VolBr
