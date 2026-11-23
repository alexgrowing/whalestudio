import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ProjExists
import Development.AbelianVarietyTheory.Definitions.Foundations.StrictInterlaceIffDescEnum
open Formalism.L2.Theta

namespace GlobalTheory.SignedHC.GridData

def mergedDecreasingWordPiZeroDZero (G : GridData) (p : ℕ) : ℚ :=
  if p ≤ G.m then G.a p
  else if p ≤ G.m + 2 * (G.k - 1) then
    (if (p - G.m) % 2 = 1 then (G.v ((p - G.m + 3) / 2) : ℚ) else G.vHalf ((p - G.m + 2) / 2))
  else -(G.b (p - G.m - 2 * (G.k - 1)) : ℚ)

def mergedDecreasingWordParity (G : GridData) (p : ℕ) : Bool := decide ((G.m + p) % 2 = 1)

theorem merged_word_succ_lt (G : GridData) (hga : 0 < G.ga) (hvb : 1 ≤ G.v G.k + G.b 1) {p : ℕ}
    (hp : p < 2 * G.m + 2 * (G.k - 1)) : G.mergedDecreasingWordPiZeroDZero (p + 1) < G.mergedDecreasingWordPiZeroDZero p := by
  have k2 := G.two_le_k
  have hg : (0 : ℚ) < G.ga := by exact_mod_cast hga
  unfold mergedDecreasingWordPiZeroDZero
  rcases lt_trichotomy p G.m with h | rfl | h
  · rw [if_pos (by omega : p + 1 ≤ G.m), if_pos h.le, G.a_eq_succ_add p]; linarith
  · rw [if_neg (by omega), if_pos (by omega), if_pos (by omega), if_pos le_rfl,
      show (G.m + 1 - G.m + 3) / 2 = 2 by omega, G.a_m]
    linarith
  · rw [if_neg (show ¬ p + 1 ≤ G.m by omega), if_neg (show ¬ p ≤ G.m by omega)]
    rcases lt_trichotomy p (G.m + 2 * (G.k - 1)) with h' | h' | h'
    · rw [if_pos (show p + 1 ≤ G.m + 2 * (G.k - 1) by omega), if_pos h'.le]
      by_cases hj : (p - G.m) % 2 = 1
      · rw [if_neg (show ¬ (p + 1 - G.m) % 2 = 1 by omega), if_pos hj, show (p + 1 - G.m + 2) / 2 = (p - G.m + 3) / 2 by omega, vHalf]
        linarith
      · rw [if_pos (show (p + 1 - G.m) % 2 = 1 by omega), if_neg hj, show (p + 1 - G.m + 3) / 2 = (p - G.m + 2) / 2 + 1 by omega, vHalf]
        have := G.v_anti ((p - G.m + 2) / 2) ((p - G.m + 2) / 2 + 1) (by omega) (by omega) (by omega)
        have : ((G.v ((p - G.m + 2) / 2 + 1) : ℤ) : ℚ) + 1 ≤ (G.v ((p - G.m + 2) / 2) : ℚ) := by
          exact_mod_cast this
        linarith
    · subst h'
      rw [if_neg (show ¬ G.m + 2 * (G.k - 1) + 1 ≤ G.m + 2 * (G.k - 1) by omega), if_pos le_rfl,
        if_neg (show ¬ (G.m + 2 * (G.k - 1) - G.m) % 2 = 1 by omega),
        show G.m + 2 * (G.k - 1) + 1 - G.m - 2 * (G.k - 1) = 1 by omega,
        show (G.m + 2 * (G.k - 1) - G.m + 2) / 2 = G.k by omega, vHalf]
      have : (1 : ℚ) ≤ (G.v G.k : ℚ) + (G.b 1 : ℚ) := by exact_mod_cast hvb
      linarith
    · rw [if_neg (show ¬ p + 1 ≤ G.m + 2 * (G.k - 1) by omega), if_neg (show ¬ p ≤ G.m + 2 * (G.k - 1) by omega),
        show p + 1 - G.m - 2 * (G.k - 1) = (p - G.m - 2 * (G.k - 1)) + 1 by omega]
      have := G.b_mono (p - G.m - 2 * (G.k - 1)) (p - G.m - 2 * (G.k - 1) + 1) (by omega) (by omega) (by omega)
      have : ((G.b (p - G.m - 2 * (G.k - 1)) : ℤ) : ℚ) < (G.b (p - G.m - 2 * (G.k - 1) + 1) : ℚ) := by
        exact_mod_cast this
      linarith

theorem merged_word_strict_anti (G : GridData) (hga : 0 < G.ga) (hvb : 1 ≤ G.v G.k + G.b 1) {p p' : ℕ} (h : p < p')
    (hp' : p' ≤ 2 * G.m + 2 * (G.k - 1)) : G.mergedDecreasingWordPiZeroDZero p' < G.mergedDecreasingWordPiZeroDZero p := by
  induction p' with
  | zero => omega
  | succ p' ih =>
    have h1 := G.merged_word_succ_lt hga hvb (p := p') (by omega)
    rcases Nat.lt_succ_iff_lt_or_eq.1 h with h | rfl
    · exact h1.trans (ih h (by omega))
    · exact h1

end GlobalTheory.SignedHC.GridData

namespace GlobalTheory.SignedHC.GridData

theorem exists_pos_of_mem_lam (G : GridData) {x : ℚ × Bool} (hx : x ∈ G.lam) :
    ∃ p ≤ 2 * G.m + 2 * (G.k - 1), x.1 = G.mergedDecreasingWordPiZeroDZero p ∧ (!x.2) = G.mergedDecreasingWordParity p := by
  have k2 := G.two_le_k
  rcases mem_lam.1 hx with ⟨i, hi, rfl⟩ | ⟨hc, hs⟩
  · refine ⟨i, by omega, by simp [mergedDecreasingWordPiZeroDZero, hi], ?_⟩
    simp only [mergedDecreasingWordParity, Nat.even_iff]
    by_cases h : (G.m - i) % 2 = 0
    · simp [h]; omega
    · simp [h]; omega
  · obtain ⟨i, hi2, hik, hv⟩ := mem_cloudHalf.1 hc
    refine ⟨G.m + 2 * i - 2, by omega, ?_, ?_⟩
    · rw [hv, mergedDecreasingWordPiZeroDZero, if_neg (show ¬ G.m + 2 * i - 2 ≤ G.m by omega),
        if_pos (show G.m + 2 * i - 2 ≤ G.m + 2 * (G.k - 1) by omega),
        if_neg (show ¬ (G.m + 2 * i - 2 - G.m) % 2 = 1 by omega),
        show (G.m + 2 * i - 2 - G.m + 2) / 2 = i by omega]
    · rw [hs, mergedDecreasingWordParity]; simp; omega

theorem exists_position_of_mem_D0 (G : GridData) {x : ℚ × Bool} (hx : x ∈ G.parD0) :
    ∃ p ≤ 2 * G.m + 2 * (G.k - 1), x.1 = G.mergedDecreasingWordPiZeroDZero p ∧ x.2 = G.mergedDecreasingWordParity p := by
  have k2 := G.two_le_k
  rcases mem_discrete_parameter_iff.1 hx with ⟨hc, hs⟩ | ⟨l, hl1, hlm, rfl⟩
  · obtain ⟨i, hi2, hik, hv⟩ := mem_cloud.1 hc
    refine ⟨G.m + 2 * i - 3, by omega, ?_, ?_⟩
    · rw [hv, mergedDecreasingWordPiZeroDZero, if_neg (show ¬ G.m + 2 * i - 3 ≤ G.m by omega),
        if_pos (show G.m + 2 * i - 3 ≤ G.m + 2 * (G.k - 1) by omega),
        if_pos (show (G.m + 2 * i - 3 - G.m) % 2 = 1 by omega),
        show (G.m + 2 * i - 3 - G.m + 3) / 2 = i by omega]
    · rw [hs, mergedDecreasingWordParity]; simp; omega
  · refine ⟨G.m + 2 * (G.k - 1) + l, by omega, ?_, ?_⟩
    · rw [mergedDecreasingWordPiZeroDZero, if_neg (show ¬ G.m + 2 * (G.k - 1) + l ≤ G.m by omega),
        if_neg (show ¬ G.m + 2 * (G.k - 1) + l ≤ G.m + 2 * (G.k - 1) by omega),
        show G.m + 2 * (G.k - 1) + l - G.m - 2 * (G.k - 1) = l by omega]
    · simp only [mergedDecreasingWordParity, Nat.even_iff]
      by_cases h : (l - 1) % 2 = 0
      · simp [h]; omega
      · simp [h]; omega

theorem mem_of_pos (G : GridData) {p : ℕ} (hp : p ≤ 2 * G.m + 2 * (G.k - 1)) :
    (∃ x ∈ G.lam, x.1 = G.mergedDecreasingWordPiZeroDZero p) ∨ ∃ x ∈ G.parD0, x.1 = G.mergedDecreasingWordPiZeroDZero p := by
  have k2 := G.two_le_k
  by_cases h1 : p ≤ G.m
  · exact Or.inl ⟨(G.a p, decide (Even (G.m - p))), mem_lam.2 (Or.inl ⟨p, h1, rfl⟩), by simp [mergedDecreasingWordPiZeroDZero, h1]⟩
  by_cases h2 : p ≤ G.m + 2 * (G.k - 1)
  · by_cases h3 : (p - G.m) % 2 = 1
    · refine Or.inr ⟨((G.v ((p - G.m + 3) / 2) : ℚ), true), mem_discrete_parameter_iff.2 (Or.inl ⟨mem_cloud.2 ⟨_, by omega, by omega, rfl⟩, rfl⟩), ?_⟩
      simp [mergedDecreasingWordPiZeroDZero, h1, h2, h3]
    · refine Or.inl ⟨(G.vHalf ((p - G.m + 2) / 2), true), mem_lam.2 (Or.inr ⟨mem_cloudHalf.2 ⟨_, by omega, by omega, rfl⟩, rfl⟩), ?_⟩
      simp [mergedDecreasingWordPiZeroDZero, h1, h2, h3]
  · refine Or.inr ⟨(-(G.b (p - G.m - 2 * (G.k - 1)) : ℚ), decide (Even (p - G.m - 2 * (G.k - 1) - 1))),
      mem_discrete_parameter_iff.2 (Or.inr ⟨_, by omega, by omega, rfl⟩), ?_⟩
    simp [mergedDecreasingWordPiZeroDZero, h1, h2]

theorem interlaced_pi_zero_and_D0 : ∀ {G : GlobalTheory.SignedHC.GridData} {n : ℕ} {lam : Fin (n + 1) → ℝ} {ε : Fin (n + 1) → Bool}
    {mu : Fin n → ℝ} {ε' : Fin n → Bool}, 0 < G.ga → 1 ≤ G.v G.k + G.b 1 → IsEnum (G.parPi 0) lam ε →
    IsEnum G.parD0 mu ε' → GlobalTheory.SepReal.Interlaced ε lam ε' mu := by
  intro G n lam ε mu ε' hga hvb ⟨hA, q, hq, hS⟩ ⟨hB, q', hq', hD⟩ x y hlt hbtw
  rw [parPi_zero] at hS
  set N := 2 * G.m + 2 * (G.k - 1) with hN
  have hV : ∀ z : Fin (n + 1) ⊕ Fin n, Sum.elim lam mu z = ((Sum.elim q q' z : ℚ) : ℝ) := by
    rintro (a | b)
    · exact hq a
    · exact hq' b
  have key : ∀ z : Fin (n + 1) ⊕ Fin n, ∃ p ≤ N, Sum.elim q q' z = G.mergedDecreasingWordPiZeroDZero p ∧
      xor (Sum.elim ε ε' z) z.isLeft = G.mergedDecreasingWordParity p := by
    rintro (a | b)
    · have hm : (q a, ε a) ∈ G.lam := by rw [hS]; exact Finset.mem_image_of_mem _ (Finset.mem_univ a)
      obtain ⟨p, hp, h1, h2⟩ := G.exists_pos_of_mem_lam hm
      refine ⟨p, hp, h1, ?_⟩
      simpa using h2
    · have hm : (q' b, ε' b) ∈ G.parD0 := by rw [hD]; exact Finset.mem_image_of_mem _ (Finset.mem_univ b)
      obtain ⟨p, hp, h1, h2⟩ := G.exists_position_of_mem_D0 hm
      refine ⟨p, hp, h1, ?_⟩
      simpa using h2
  have surj : ∀ p ≤ N, ∃ z : Fin (n + 1) ⊕ Fin n, Sum.elim q q' z = G.mergedDecreasingWordPiZeroDZero p := by
    intro p hp
    rcases G.mem_of_pos hp with ⟨x, hx, hx1⟩ | ⟨x, hx, hx1⟩
    · rw [hS] at hx
      obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hx
      exact ⟨Sum.inl a, hx1⟩
    · rw [hD] at hx
      obtain ⟨b, -, rfl⟩ := Finset.mem_image.1 hx
      exact ⟨Sum.inr b, hx1⟩
  obtain ⟨px, hpx, hx1, hx2⟩ := key x
  obtain ⟨py, hpy, hy1, hy2⟩ := key y
  rw [hV, hV, hx1, hy1, Rat.cast_lt] at hlt
  have hlt' : px < py := by
    by_contra h
    rcases (not_lt.1 h).eq_or_lt with h | h
    · subst h; exact lt_irrefl _ hlt
    · exact lt_asymm hlt (G.merged_word_strict_anti hga hvb h hpx)
  have hsucc : py = px + 1 := by
    by_contra h
    obtain ⟨z, hz⟩ := surj (px + 1) (by omega)
    refine hbtw z ⟨?_, ?_⟩
    · rw [hV, hV, hy1, hz, Rat.cast_lt]; exact G.merged_word_strict_anti hga hvb (by omega) hpy
    · rw [hV, hV, hx1, hz, Rat.cast_lt]; exact G.merged_word_strict_anti hga hvb (Nat.lt_succ_self px) (by omega)
  have hpar : G.mergedDecreasingWordParity py = !G.mergedDecreasingWordParity px := by
    subst hsucc; simp only [mergedDecreasingWordParity]
    by_cases h : (G.m + px) % 2 = 1
    · simp [h]; omega
    · simp [h]; omega
  rw [← hx2, ← hy2] at hpar
  revert hpar
  cases Sum.elim ε ε' x <;> cases Sum.elim ε ε' y <;> cases x.isLeft <;> cases y.isLeft <;> decide

end GlobalTheory.SignedHC.GridData
