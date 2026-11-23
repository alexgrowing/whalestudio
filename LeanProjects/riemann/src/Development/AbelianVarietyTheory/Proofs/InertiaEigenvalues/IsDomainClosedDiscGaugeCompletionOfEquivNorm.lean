import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemBallOfGaugeLt

open scoped NNReal

namespace GlobalTheory.BSP.DiscDomain

variable {l : ℕ} [hl : Fact l.Prime] {A : Type} [CommRing A] {u : A} {ρ : ℝ≥0}

private theorem gauge_mul_le_of_mem_ball (y z : PreDisc l u ρ) {s : ℝ} (hs : 0 < s) (hz : z ∈ ball l u ρ s) :
    gauge l u ρ (y * z) ≤ gauge l u ρ y * s := by
  have key : ∀ r, gauge l u ρ y < r → gauge l u ρ (y * z) / s ≤ r := by
    intro r hr
    have hr0 : 0 < r := (gauge_nonneg l u ρ y).trans_lt hr
    rw [div_le_iff₀ hs]
    exact gauge_le l u ρ (mul_pos hr0 hs)
      (mul_mem_ball l u ρ hr0.le (mem_ball_of_gauge_lt l u ρ hr) hz)
  rw [← div_le_iff₀ hs]
  exact le_of_forall_gt_imp_ge_of_dense key

private theorem algebraMap_natCast_mem_ball_inv (hl0 : (0 : ℝ) < l) :
    algebraMap A (PreDisc l u ρ) (l : A) ∈ ball l u ρ ((l : ℝ)⁻¹) := by
  refine Submodule.subset_span ?_
  rw [monos, Set.mem_setOf_eq]
  refine ⟨1, 0, 0, ?_, ?_⟩
  · rw [pow_zero, pow_zero, pow_one, one_mul, inv_mul_cancel₀ hl0.ne']
  · simp

private theorem invSelf_mem_ball :
    (IsLocalization.Away.invSelf (l : A) : PreDisc l u ρ) ∈ ball l u ρ (l : ℝ) := by
  refine Submodule.subset_span ?_
  rw [monos, Set.mem_setOf_eq]
  refine ⟨0, 0, 1, ?_, ?_⟩
  · simp
  · simp

theorem norm_mul_l (y : PreDisc l u ρ) :
    ‖y * algebraMap A (PreDisc l u ρ) (l : A)‖ * l = ‖y‖ := by
  have hl0 : (0 : ℝ) < l := by exact_mod_cast hl.out.pos
  rw [norm_preDisc, norm_preDisc]
  apply le_antisymm
  · have h := gauge_mul_le_of_mem_ball y _ (inv_pos.mpr hl0) (algebraMap_natCast_mem_ball_inv (u := u) (ρ := ρ) hl0)
    calc gauge l u ρ (y * algebraMap A (PreDisc l u ρ) (l : A)) * l
        ≤ gauge l u ρ y * (l : ℝ)⁻¹ * l := mul_le_mul_of_nonneg_right h hl0.le
      _ = gauge l u ρ y := by rw [mul_assoc, inv_mul_cancel₀ hl0.ne', mul_one]
  · have h := gauge_mul_le_of_mem_ball (y * algebraMap A (PreDisc l u ρ) (l : A)) _ hl0
      (invSelf_mem_ball (u := u) (ρ := ρ))
    rwa [mul_assoc, IsLocalization.Away.mul_invSelf, mul_one] at h

theorem norm_mul_l_pow (n : ℕ) (y : PreDisc l u ρ) :
    ‖y * algebraMap A (PreDisc l u ρ) (l : A) ^ n‖ * (l : ℝ) ^ n = ‖y‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h := norm_mul_l (y * algebraMap A (PreDisc l u ρ) (l : A) ^ n)
    calc ‖y * algebraMap A (PreDisc l u ρ) (l : A) ^ (n + 1)‖ * (l : ℝ) ^ (n + 1)
        = ‖y * algebraMap A (PreDisc l u ρ) (l : A) ^ n * algebraMap A (PreDisc l u ρ) (l : A)‖ * l
            * (l : ℝ) ^ n := by
          rw [pow_succ, pow_succ, mul_assoc y]; ring
      _ = ‖y‖ := by rw [h, ih]

private theorem exists_mul_pow_eq_algebraMap (p : PreDisc l u ρ) :
    ∃ (a : A) (k : ℕ), p * algebraMap A (PreDisc l u ρ) (l : A) ^ k = algebraMap A (PreDisc l u ρ) a := by
  obtain ⟨⟨a, s⟩, h⟩ := IsLocalization.surj (Submonoid.powers (l : A)) p
  obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff _ _).mp s.2
  refine ⟨a, k, ?_⟩
  rw [← map_pow, hk]
  exact h

private theorem norm_ofPre_eq_mul_pow {p : PreDisc l u ρ} {a : A} {k : ℕ}
    (h : p * algebraMap A (PreDisc l u ρ) (l : A) ^ k = algebraMap A (PreDisc l u ρ) a) :
    ‖ofPre l u ρ p‖ = ‖toDisc l u ρ a‖ * (l : ℝ) ^ k := by
  have e : ‖toDisc l u ρ a‖ = ‖algebraMap A (PreDisc l u ρ) a‖ := by
    rw [toDisc, RingHom.comp_apply, norm_ofPre, norm_preDisc]
  rw [e, ← h, norm_mul_l_pow, norm_ofPre, norm_preDisc]

private theorem sq_mul_norm_mul_norm_le_norm_mul (N : A → ℝ) (c : ℝ) (hc : 0 < c) (hmul : ∀ x y, N (x * y) = N x * N y)
    (hle : ∀ x, N x ≤ ‖toDisc l u ρ x‖) (hge : ∀ x, c * ‖toDisc l u ρ x‖ ≤ N x) (p q : PreDisc l u ρ) :
    c ^ 2 * (‖ofPre l u ρ p‖ * ‖ofPre l u ρ q‖) ≤ ‖ofPre l u ρ p * ofPre l u ρ q‖ := by
  obtain ⟨a, k, hp⟩ := exists_mul_pow_eq_algebraMap p
  obtain ⟨b, m, hq⟩ := exists_mul_pow_eq_algebraMap q
  have hpq : p * q * algebraMap A (PreDisc l u ρ) (l : A) ^ (k + m) =
      algebraMap A (PreDisc l u ρ) (a * b) := by
    rw [map_mul, ← hp, ← hq, pow_add]; ring
  rw [← map_mul, norm_ofPre_eq_mul_pow hp, norm_ofPre_eq_mul_pow hq, norm_ofPre_eq_mul_pow hpq, pow_add]
  have hab : N a * N b ≤ ‖toDisc l u ρ (a * b)‖ := by rw [← hmul]; exact hle _
  have h0 : 0 ≤ c * ‖toDisc l u ρ a‖ := mul_nonneg hc.le (norm_nonneg _)
  have h1 : 0 ≤ c * ‖toDisc l u ρ b‖ := mul_nonneg hc.le (norm_nonneg _)
  have key : c * ‖toDisc l u ρ a‖ * (c * ‖toDisc l u ρ b‖) ≤ ‖toDisc l u ρ (a * b)‖ :=
    (mul_le_mul (hge a) (hge b) h1 (h0.trans (hge a))).trans hab
  have hpow : 0 ≤ (l : ℝ) ^ k * (l : ℝ) ^ m := by positivity
  calc c ^ 2 * (‖toDisc l u ρ a‖ * (l : ℝ) ^ k * (‖toDisc l u ρ b‖ * (l : ℝ) ^ m))
      = c * ‖toDisc l u ρ a‖ * (c * ‖toDisc l u ρ b‖) * ((l : ℝ) ^ k * (l : ℝ) ^ m) := by ring
    _ ≤ ‖toDisc l u ρ (a * b)‖ * ((l : ℝ) ^ k * (l : ℝ) ^ m) := mul_le_mul_of_nonneg_right key hpow

theorem isDomain_disc (l : ℕ) [hl : Fact l.Prime] (A : Type) [CommRing A] (u : A) (ρ : ℝ≥0) (N : A → ℝ) (c : ℝ)
    (hc : 0 < c) (hmul : ∀ x y, N (x * y) = N x * N y) (_hadd : ∀ x y, N (x + y) ≤ max (N x) (N y))
    (hNl : N (l : A) = (l : ℝ)⁻¹) (hle : ∀ x, N x ≤ ‖toDisc l u ρ x‖) (hge : ∀ x, c * ‖toDisc l u ρ x‖ ≤ N x) :
    IsDomain (Disc l u ρ) ∧ ∀ x y : Disc l u ρ, c ^ 2 * (‖x‖ * ‖y‖) ≤ ‖x * y‖ := by
  have hmain : ∀ x y : Disc l u ρ, c ^ 2 * (‖x‖ * ‖y‖) ≤ ‖x * y‖ := by
    intro x y
    refine (denseRange_ofPre l u ρ).induction_on₂
      (p := fun x y : Disc l u ρ => c ^ 2 * (‖x‖ * ‖y‖) ≤ ‖x * y‖) ?_ ?_ x y
    · exact isClosed_le (by fun_prop) (by fun_prop)
    · intro p q
      exact sq_mul_norm_mul_norm_le_norm_mul N c hc hmul hle hge p q
  have hlinv : (0 : ℝ) < (l : ℝ)⁻¹ := inv_pos.mpr (by exact_mod_cast hl.out.pos)
  have hne : toDisc l u ρ (l : A) ≠ 0 := by
    intro h
    have h' := hle (l : A)
    rw [h, norm_zero, hNl] at h'
    linarith
  haveI : Nontrivial (Disc l u ρ) := ⟨⟨_, _, hne⟩⟩
  haveI : NoZeroDivisors (Disc l u ρ) := by
    refine ⟨fun {x y} hxy => ?_⟩
    have h := hmain x y
    rw [hxy, norm_zero] at h
    have hc2 : 0 < c ^ 2 := by positivity
    have hn : ‖x‖ * ‖y‖ ≤ 0 := by nlinarith [mul_nonneg (norm_nonneg x) (norm_nonneg y)]
    rcases mul_eq_zero.mp (le_antisymm hn (mul_nonneg (norm_nonneg _) (norm_nonneg _))) with h | h
    · exact Or.inl (norm_eq_zero.mp h)
    · exact Or.inr (norm_eq_zero.mp h)
  exact ⟨NoZeroDivisors.to_isDomain (α := Disc l u ρ), hmain⟩

end GlobalTheory.BSP.DiscDomain
