import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GapCondExample

namespace GlobalTheory.CompanionTheory.Ar.Crv.Chain

open GlobalTheory.CompanionTheory.Ar.Crv

theorem abel_bound (ν v : ℕ → ℝ) (P : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (hν : ∀ i, 1 ≤ i → i < n → ν (i + 1) ≤ ν i) (hv : ∀ i, i ≤ n → v i ≤ P) :
    ∑ i ∈ Finset.range n, ν (i + 1) * (v (i + 1) - v i) ≤
      ν n * v n - ν 1 * v 0 + P * (ν 1 - ν n) := by
  induction n, hn using Nat.le_induction with
  | base => simp; linarith
  | succ n hn ih =>
    rw [Finset.sum_range_succ]
    have h1 := ih (fun i h h' => hν i h (by omega)) (fun i h => hv i (by omega))
    have h2 := hν n hn (by omega)
    have h3 := hv n (by omega)
    nlinarith [mul_nonneg (sub_nonneg.2 h2) (sub_nonneg.2 h3)]

theorem lmuNum_nonneg : ∀ (T : Type) [Fintype T] (p j q : ℕ) (μ w l : T → ℕ → ℝ) (P e : ℝ), 2 < p → 1 ≤ j → 1 ≤ q → GapCond p j q μ → (∀ τ, w τ 0 = 0) → (∀ τ, l τ 0 = 0) → (∀ τ i, i ≤ j → w τ i ≤ P) → (∀ τ i, i ≤ q → l τ i ≤ P) → (∀ τ, w τ j = l τ q) → e = -2 * ∑ τ, w τ j → ((p : ℝ) - 2) * P ≤ e → 0 ≤ e → 0 ≤ lmuNum j q μ w l := by
  intro T _ p j q μ w l P e hp hj hq hgap hw0 hl0 hw hl hwl he hPe he0
  obtain ⟨hdom, M, g, hM, hg, hpg⟩ := hgap
  rcases isEmpty_or_nonempty T with hT | ⟨⟨τ₀⟩⟩
  · simp [lmuNum]
  have hp' : (0 : ℝ) < (p : ℝ) - 2 := by
    have : (2 : ℝ) < p := by exact_mod_cast hp
    linarith
  have hP : 0 ≤ P := by have := hw τ₀ 0 (by omega); rwa [hw0] at this
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM τ₀ 1 le_rfl (by omega))
  have hf : (0 : ℝ) ≤ (Fintype.card T : ℝ) := Nat.cast_nonneg _
  have hfM : 0 ≤ (Fintype.card T : ℝ) * M := mul_nonneg hf hM0
  have hg0 : 0 ≤ g := by
    by_contra h
    push Not at h
    nlinarith [mul_pos hp' (neg_pos.2 h)]
  have key : ∀ τ, (∑ i ∈ Finset.range j, μ τ (i + 1) * (w τ (i + 1) - w τ i)) +
      ∑ m ∈ Finset.range q, μ τ (j + m + 1) * (l τ (q - m - 1) - l τ (q - m)) ≤
      g * w τ j + 2 * M * P := by
    intro τ
    have hA := abel_bound (μ τ) (w τ) P j hj (fun i h h' => hdom τ i h (by omega)) (hw τ)
    have hB := abel_bound (fun i => μ τ (j + i)) (fun m => l τ (q - m)) P q hq
      (fun i h h' => hdom τ (j + i) (by omega) (by omega)) (fun i _ => hl τ _ (by omega))
    simp only [Nat.sub_self, Nat.sub_zero, hl0, ← hwl τ] at hB
    rw [hw0] at hA
    have e1 : ∑ m ∈ Finset.range q, μ τ (j + m + 1) * (l τ (q - m - 1) - l τ (q - m)) =
        ∑ m ∈ Finset.range q, μ τ (j + (m + 1)) * (l τ (q - (m + 1)) - l τ (q - m)) := rfl
    rw [e1]
    have h1 := abs_le.1 (hM τ 1 le_rfl (by omega))
    have h2 := abs_le.1 (hM τ (j + q) (by omega) le_rfl)
    have h3 := mul_nonneg (sub_nonneg.2 (hg τ)) (sub_nonneg.2 (hw τ j le_rfl))
    have h4 : 0 ≤ P * (2 * M - (μ τ 1 - μ τ (j + q))) := mul_nonneg hP (by linarith [h1.2, h2.1])
    have h5 := mul_nonneg hg0 hP
    nlinarith
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun τ _ => key τ)
  rw [Finset.sum_add_distrib (f := fun τ => g * w τ j), ← Finset.mul_sum] at hsum
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
  have hS : ∑ τ, w τ j = -e / 2 := by linarith
  rw [hS] at hsum
  have hfin : g * (-e / 2) + (Fintype.card T : ℝ) * (2 * M * P) ≤ 0 := by
    have a1 := mul_le_mul_of_nonneg_left hPe hfM
    have a2 := mul_le_mul_of_nonneg_right hpg he0
    by_contra h
    push Not at h
    nlinarith [mul_pos hp' h]
  unfold lmuNum
  linarith

end GlobalTheory.CompanionTheory.Ar.Crv.Chain
