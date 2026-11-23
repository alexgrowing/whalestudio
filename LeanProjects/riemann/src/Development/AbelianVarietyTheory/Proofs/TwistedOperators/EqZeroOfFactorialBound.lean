import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SameBlockOfPosC
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible

namespace GlobalTheory.FactorialJet

open Set Filter Topology

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem norm_le_right (g : ℕ → ℝ → E) (C ρ t0 : ℝ)
    (hd : ∀ k t, HasDerivAt (g k) (g (k + 1) t) t)
    (hb : ∀ k t, ‖g k t‖ ≤ C * ρ ^ k * (k.factorial : ℝ)) (h0 : ∀ k, g k t0 = 0) (n : ℕ) :
    ∀ k t, t0 ≤ t →
      ‖g k t‖ ≤ C * ρ ^ (k + n) * ((k + n).factorial : ℝ) * ((t - t0) ^ n / (n.factorial : ℝ)) := by
  induction n with
  | zero => intro k t _; simpa using hb k t
  | succ n ih =>
    intro k t ht
    set A : ℝ := C * ρ ^ (k + (n + 1)) * ((k + (n + 1)).factorial : ℝ) with hA
    have hB : ∀ x : ℝ, HasDerivAt (fun s : ℝ => A * ((s - t0) ^ (n + 1) / ((n + 1).factorial : ℝ)))
        (A * ((x - t0) ^ n / (n.factorial : ℝ))) x := by
      intro x
      have h1 : HasDerivAt (fun s : ℝ => (s - t0) ^ (n + 1)) (((n + 1 : ℕ) : ℝ) * (x - t0) ^ n * 1) x := by
        exact ((hasDerivAt_id x).sub_const t0).pow (n + 1)
      have h2 := (h1.div_const ((n + 1).factorial : ℝ)).const_mul A
      refine h2.congr_deriv ?_
      congr 1
      rw [Nat.factorial_succ]
      have : (n.factorial : ℝ) ≠ 0 := by positivity
      have : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
      push_cast at *
      field_simp
    have := image_norm_le_of_norm_deriv_right_le_deriv_boundary (f := g k) (f' := g (k + 1))
      (a := t0) (b := t) (fun x _ => (hd k x).continuousAt.continuousWithinAt)
      (fun x _ => (hd k x).hasDerivWithinAt) (by simp [h0 k]) hB
      (fun x hx => by
        have h := ih (k + 1) x hx.1
        have e : k + 1 + n = k + (n + 1) := by ring
        rwa [e] at h) (x := t) ⟨ht, le_rfl⟩
    exact this

theorem eq_zero_near_right (g : ℕ → ℝ → E) (C ρ t0 : ℝ) (hρ : 0 < ρ)
    (hd : ∀ k t, HasDerivAt (g k) (g (k + 1) t) t)
    (hb : ∀ k t, ‖g k t‖ ≤ C * ρ ^ k * (k.factorial : ℝ)) (h0 : ∀ k, g k t0 = 0)
    (k : ℕ) (t : ℝ) (ht : t0 ≤ t) (ht' : ρ * (t - t0) < 1) : g k t = 0 := by
  have hr : ‖ρ * (t - t0)‖ < 1 := by
    rw [Real.norm_of_nonneg (mul_nonneg hρ.le (sub_nonneg.2 ht))]; exact ht'
  have hs := (summable_choose_mul_geometric_of_norm_lt_one k hr).tendsto_atTop_zero
  have hs2 := hs.const_mul (C * ρ ^ k * (k.factorial : ℝ))
  rw [mul_zero] at hs2
  have hle : ‖g k t‖ ≤ 0 := by
    refine ge_of_tendsto' hs2 fun n => ?_
    have h := norm_le_right g C ρ t0 hd hb h0 n k t ht
    refine h.trans (le_of_eq ?_)
    have e : ((k + n).factorial : ℝ) = ((n + k).choose k : ℝ) * n.factorial * k.factorial := by
      rw [add_comm k n]; exact_mod_cast (Nat.add_choose_mul_factorial_mul_factorial n k).symm
    have : (n.factorial : ℝ) ≠ 0 := by positivity
    rw [e, mul_pow, pow_add]
    field_simp
  exact norm_le_zero_iff.1 hle

theorem eq_zero_right (g : ℕ → ℝ → E) (C ρ : ℝ) (hρ : 0 < ρ)
    (hd : ∀ k t, HasDerivAt (g k) (g (k + 1) t) t)
    (hb : ∀ k t, ‖g k t‖ ≤ C * ρ ^ k * (k.factorial : ℝ)) (h0 : ∀ k, g k 0 = 0)
    (k : ℕ) (t : ℝ) (ht : 0 ≤ t) : g k t = 0 := by
  have key : ∀ m : ℕ, ∀ k (t : ℝ), 0 ≤ t → 2 * ρ * t ≤ m → g k t = 0 := by
    intro m
    induction m with
    | zero =>
      intro k t ht h
      have : t = 0 := by
        have : t ≤ 0 := by
          by_contra hc
          push_neg at hc
          have := mul_pos hρ hc
          simp at h
          nlinarith
        linarith
      rw [this, h0]
    | succ m ih =>
      intro k t ht h
      by_cases hm : 2 * ρ * t ≤ m
      · exact ih k t ht hm
      · push_neg at hm
        have e : 2 * ρ * ((m : ℝ) / (2 * ρ)) = m := by field_simp
        have h1 : (m : ℝ) / (2 * ρ) ≤ t := by
          rw [div_le_iff₀ (by positivity)]; linarith
        refine eq_zero_near_right g C ρ ((m : ℝ) / (2 * ρ)) hρ hd hb
          (fun j => ih j _ (by positivity) e.le) k t h1 ?_
        push_cast at h
        linarith
  exact key ⌈2 * ρ * t⌉₊ k t ht (Nat.le_ceil _)

theorem eq_zero_of_factorial_bound :
    ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (g : ℕ → ℝ → E) (C ρ : ℝ), 0 ≤ C → 0 < ρ → (∀ k t, HasDerivAt (g k) (g (k + 1) t) t) → (∀ k t, ‖g k t‖ ≤ C * ρ ^ k * (k.factorial : ℝ)) → (∀ k, g k 0 = 0) → ∀ k t, g k t = 0 := by
  intro E _ _ g C ρ _ hρ hd hb h0 k t
  rcases le_total 0 t with ht | ht
  · exact eq_zero_right g C ρ hρ hd hb h0 k t ht
  · have h := eq_zero_right (fun j s => ((-1 : ℝ) ^ j) • g j (-s)) C ρ hρ
      (fun j s => by
        have h1 := ((hd j (-s)).scomp s (hasDerivAt_neg s)).const_smul ((-1 : ℝ) ^ j)
        refine h1.congr_deriv ?_
        rw [smul_smul, pow_succ])
      (fun j s => by simpa [norm_smul] using hb j (-s))
      (fun j => by simp [h0 j]) k (-t) (by linarith)
    simpa using h

end GlobalTheory.FactorialJet
