import Mathlib
import GroundTheory.HeightsAndTheta.Heights.MultinomialWeights.StatementsEnd
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.TheoremB

open Finset

theorem inertFrob_snd {d : IndexData} {φ : Equiv.Perm (Emb d)} (hφ : IsFrobLike d φ)
    (hi : IsInertFrob d φ) (e : Emb d) : (φ e).2 = !e.2 := by
  obtain ⟨σ, b⟩ := e
  cases b with
  | false => simpa using hi σ
  | true =>
    have h := hφ.1 (σ, false)
    have hc : conjEmb d (σ, false) = (σ, true) := rfl
    rw [hc] at h
    rw [h]
    simp [conjEmb, hi σ]

theorem inertFrob_pow_snd {d : IndexData} {φ : Equiv.Perm (Emb d)} (hφ : IsFrobLike d φ)
    (hi : IsInertFrob d φ) (e : Emb d) (n : ℕ) : ((φ ^ n) e).2 = (e.2 ^^ decide (Odd n)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, inertFrob_snd hφ hi, ih]
    cases e.2 <;> by_cases h : Odd n <;> simp [h, Nat.odd_add_one]

theorem rankLie_inert_pow {d : IndexData} {φ : Equiv.Perm (Emb d)} (hφ : IsFrobLike d φ)
    (hi : IsInertFrob d φ) (τ : Fin d.f) (n : ℕ) :
    rankLie d ((φ ^ (n + 1)) (τ, false)) = if Odd n then d.j else d.N - d.j := by
  unfold rankLie
  rw [inertFrob_pow_snd hφ hi]
  by_cases h : Odd n <;> simp [h, Nat.odd_add_one]

theorem KaPInert.proof : KaPInert.Statement := by
  intro d p φ hp hφ hi τ
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  set r : ℝ := ((p : ℝ) ^ 2)⁻¹ with hr
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := inv_lt_one_of_one_lt₀ (by nlinarith)
  set a : ℝ := ((d.N - d.j : ℕ) : ℝ)
  set t : ℕ → ℝ := fun n => ((p : ℝ) ^ (n + 1))⁻¹ * (rankLie d ((φ ^ (n + 1)) (τ, false)) : ℝ)
  have heven : ∀ k, t (2 * k) = (a / p) * r ^ k := by
    intro k
    simp only [t, rankLie_inert_pow hφ hi, hr, a]
    have : ¬ Odd (2 * k) := by simp
    rw [if_neg this, inv_pow, ← pow_mul, pow_succ]
    field_simp
  have hodd : ∀ k, t (2 * k + 1) = ((d.j : ℝ) / p ^ 2) * r ^ k := by
    intro k
    simp only [t, rankLie_inert_pow hφ hi, hr]
    have : Odd (2 * k + 1) := odd_two_mul_add_one k
    rw [if_pos this, inv_pow, ← pow_mul, show 2 * k + 1 + 1 = 2 * k + 2 by ring, pow_add]
    field_simp
  have hg : Summable (fun k : ℕ => r ^ k) := summable_geometric_of_lt_one hr0 hr1
  have hse : Summable (fun k => t (2 * k)) := by
    simp_rw [heven]; exact hg.mul_left _
  have hso : Summable (fun k => t (2 * k + 1)) := by
    simp_rw [hodd]; exact hg.mul_left _
  have hsum : kaP d p φ τ = ∑' k, t (2 * k) + ∑' k, t (2 * k + 1) :=
    (tsum_even_add_odd hse hso).symm
  rw [hsum]
  simp_rw [heven, hodd]
  rw [tsum_mul_left, tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1, hr]
  have hp2 : (p : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
  have hp2' : (1 : ℝ) - ((p : ℝ) ^ 2)⁻¹ = ((p : ℝ) ^ 2 - 1) / (p : ℝ) ^ 2 := by
    field_simp
  rw [hp2']
  field_simp

end GroundTheory.Heights₂.Heights.TheoremB
