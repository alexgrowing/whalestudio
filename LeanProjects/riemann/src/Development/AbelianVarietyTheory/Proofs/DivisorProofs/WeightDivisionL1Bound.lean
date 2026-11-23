import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DividedWeightUnique
import Formalism.MeanHeightDescent.CovolumeFullAssemblyWeighted
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedWeightEntriesSignsSizesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedWeightGapsBlockAndBarStatement

open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.L2.Indef.Tree NumberField GlobalTheory.MeanTop

namespace GlobalTheory.MeanTop

theorem Wts.divided_weight_small_block_le_neg_three_mul {ι : Type} [Fintype ι] {N : ℕ} (W : Wts ι N) (hH : W.Hyp) (hD : W.IsDiv) (τ : ι) :
    ∀ (k : ℕ) (hk : W.p + k < N), W.u1 τ ⟨W.p + k, hk⟩ ≤ -(3 * (N : ℤ)) := by
  have hT : (4 : ℤ) ≤ W.T := by have := hH.h1; omega
  intro k
  induction k with
  | zero =>
    intro hk
    have h1 := hH.kc_pos
    have h2 := hH.kc_lt
    have hg := ((GlobalTheory.T.dividedWeight_gaps_block_and_bar ι N W hH hD τ ⟨W.p - 1, by omega⟩ ⟨W.p + 0, hk⟩ (by simp; omega)).2.1 (by simp)).2
    have he := (GlobalTheory.T.dividedWeight_entries_signs_sizes ι N W hH hD τ ⟨W.p - 1, by omega⟩).2.1 (by simp; omega)
    have h3 := hH.h2.2
    have hN : (0 : ℤ) ≤ 24 * (N : ℤ) * W.T := by positivity
    have h4 : 0 ≤ W.u1 τ ⟨W.p - 1, by omega⟩ - W.u1 τ ⟨W.p + 0, hk⟩ - 3 * N := by
      by_contra hneg
      push_neg at hneg
      nlinarith
    linarith
  | succ k ih =>
    intro hk
    have h1 := ih (by omega)
    have hg := (GlobalTheory.T.dividedWeight_gaps_block_and_bar ι N W hH hD τ ⟨W.p + k, by omega⟩ ⟨W.p + (k + 1), hk⟩ (by simp; omega)).1 (by simp)
    have hN : (0 : ℤ) ≤ (W.T : ℤ) + W.Dd + 2 + 2 * N := by positivity
    linarith

theorem Wts.abs_u'_le {ι : Type} [Fintype ι] {N : ℕ} (W : Wts ι N) (hH : W.Hyp) (hD : W.IsDiv) (τ : ι) (i : Fin N) :
    |W.u' τ i| ≤ |W.u1 τ i| := by
  unfold Wts.u'
  split_ifs with h
  · exact le_rfl
  · obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (not_lt.mp h)
    have hlt : W.p + k < N := hk ▸ i.2
    have hi : i = ⟨W.p + k, hlt⟩ := Fin.ext hk
    have h1 := W.divided_weight_small_block_le_neg_three_mul hH hD τ k hlt
    rw [← hi] at h1
    have hN : (0 : ℤ) ≤ N := by positivity
    rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
    linarith

theorem divided_weight_size : ∀ (ι : Type) [Fintype ι] (N : ℕ) (W : Wts ι N), W.Hyp → W.IsDiv → (W.T : ℝ) * l1 W.u1 ≤ l1 W.u + (Fintype.card ι : ℝ) * N * (W.c0 + 4 * N) ∧ l1 W.u' ≤ l1 W.u1 ∧ ∀ τ i, |W.u' τ i| ≤ |W.u1 τ i| := by
  intro ι _ N W hH hD
  refine ⟨?_, ?_, fun τ i => W.abs_u'_le hH hD τ i⟩
  · have key : ∀ τ i, (W.T : ℝ) * |(W.u1 τ i : ℝ)| ≤ |(W.u τ i : ℝ)| + (W.c0 + 4 * N) := by
      intro τ i
      have h1 := (GlobalTheory.T.dividedWeight_entries_signs_sizes ι N W hH hD τ i).1
      have h0 : (0 : ℤ) ≤ ((W.Dd : ℤ) + 1) * |W.u1 τ i| := by positivity
      have h2 : (W.T : ℤ) * |W.u1 τ i| ≤ |W.u τ i| + (W.c0 + 4 * N) := by nlinarith
      exact_mod_cast h2
    unfold l1
    calc (W.T : ℝ) * ∑ τ, ∑ i, |(W.u1 τ i : ℝ)|
        = ∑ τ, ∑ i, (W.T : ℝ) * |(W.u1 τ i : ℝ)| := by simp only [Finset.mul_sum]
      _ ≤ ∑ τ, ∑ i : Fin N, (|(W.u τ i : ℝ)| + (W.c0 + 4 * N)) :=
          Finset.sum_le_sum fun τ _ => Finset.sum_le_sum fun i _ => key τ i
      _ = _ := by
          simp only [Finset.sum_add_distrib (f := fun i => |(W.u _ i : ℝ)|), Finset.sum_const, Finset.card_univ,
            Fintype.card_fin, nsmul_eq_mul]
          rw [Finset.sum_add_distrib]
          simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          ring
  · unfold l1
    refine Finset.sum_le_sum fun τ _ => Finset.sum_le_sum fun i _ => ?_
    exact_mod_cast W.abs_u'_le hH hD τ i

end GlobalTheory.MeanTop
