import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DividedWeightUnique
import Formalism.MeanHeightDescent.CovolumeFullAssemblyWeighted
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedWeightEntriesSignsSizes

open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.L2.Indef.Tree NumberField GlobalTheory.MeanTop

namespace GlobalTheory.MeanTop

theorem Wts.node_lower_int {ι : Type} {N : ℕ} (W : Wts ι N) (H : W.Hyp) (hd : W.IsDiv) (τ : ι) :
    ∀ (n : ℕ) (i : Fin N), (i : ℕ) + 1 = W.kc + n →
      -W.u τ i - (if W.p ≤ (i : ℕ) then W.c0 + 2 * (N : ℤ) else 0) - n * ((W.T : ℤ) + W.Dd + 1) ≤
        ((W.T : ℤ) + W.Dd + 1) * (-W.u1 τ i) := by
  intro n
  have hkp := H.kc_lt
  induction n with
  | zero =>
    intro i hi
    have h1 := (hd τ).1 i (by simpa using hi)
    have h2 := H.anchor τ i (by simpa using hi)
    have h3 : ¬ W.p ≤ (i : ℕ) := by omega
    simp [h1, h2, h3]
  | succ n ih =>
    intro i hi
    have hk := H.kc_pos
    have hlt : (i : ℕ) - 1 < N := by omega
    have hab : (i : ℕ) = ((⟨(i : ℕ) - 1, hlt⟩ : Fin N) : ℕ) + 1 := by simp; omega
    have ha : ((⟨(i : ℕ) - 1, hlt⟩ : Fin N) : ℕ) + 1 = W.kc + n := by simp; omega
    generalize (⟨(i : ℕ) - 1, hlt⟩ : Fin N) = a at hab ha
    have h1 := ih a ha
    have h2 := (hd τ).2 a i hab
    have hM : (0 : ℤ) < (W.T : ℤ) + W.Dd + 1 := by positivity
    generalize (W.T : ℤ) + W.Dd + 1 = M at h1 h2 hM ⊢
    set x := (W.u τ a - W.u τ i + if (i : ℕ) = W.p then -W.c0 - (2 * (N : ℤ) - 2) else 2) with hx
    have h3 := Int.mul_ediv_add_emod x M
    have h4 := Int.emod_lt_of_pos x hM
    rw [← h2] at h3
    have h5 : M * -W.u1 τ i = M * -W.u1 τ a + M * (W.u1 τ a - W.u1 τ i) := by ring
    have h6 : ((n + 1 : ℕ) : ℤ) * M = n * M + M := by push_cast; ring
    rw [h5, h6]
    by_cases hp : (i : ℕ) = W.p
    · have e1 : W.p ≤ (i : ℕ) := by omega
      have e2 : ¬ W.p ≤ (a : ℕ) := by omega
      rw [if_pos hp] at hx
      rw [if_neg e2] at h1
      rw [if_pos e1]
      linarith
    · rw [if_neg hp] at hx
      by_cases e1 : W.p ≤ (i : ℕ)
      · have e2 : W.p ≤ (a : ℕ) := by omega
        rw [if_pos e2] at h1
        rw [if_pos e1]
        linarith
      · have e2 : ¬ W.p ≤ (a : ℕ) := by omega
        rw [if_neg e2] at h1
        rw [if_neg e1]
        linarith

theorem nodes_far_and_spread : ∀ (ι : Type) [Fintype ι] (N : ℕ) (W : Wts ι N), W.Hyp → W.IsDiv → ∀ τ, (∀ i : Fin N, W.kc ≤ (i : ℕ) → W.w τ / (2 * W.T) ≤ -(W.u1 τ i : ℝ) ∧ W.w τ / (4 * W.T) ≤ |(W.u' τ i : ℝ)|) ∧ ∀ i l : Fin N, (W.u' τ i : ℝ) - W.u' τ l ≤ 3 / 2 * W.w τ / W.T := by
  intro ι _ N W H hd τ
  have hk := H.kc_pos
  have hkp := H.kc_lt
  have hpN := H.p_lt
  have hc0 : (0 : ℝ) ≤ W.c0 := by exact_mod_cast H.weightConst_nonneg
  have hT : 4 * (W.Dd : ℝ) + 4 ≤ W.T := by exact_mod_cast H.h1
  have hD : (0 : ℝ) ≤ W.Dd := by positivity
  have hN : (0 : ℝ) ≤ N := by positivity
  have hT0 : (0 : ℝ) < W.T := by linarith
  have hw := H.h3w τ
  have hS : 0 ≤ W.S := by
    have := H.h3cloud τ ⟨0, by omega⟩ (by simp; omega)
    have h0 : (0 : ℝ) ≤ W.u τ ⟨0, by omega⟩ := by exact_mod_cast this.1
    linarith [this.2]
  have hr : 0 ≤ W.eta + W.S + N := (abs_nonneg _).trans (H.h3node τ ⟨W.p, hpN⟩ hkp.le)
  have hNT : 4 * (N : ℝ) ≤ N * W.T := by nlinarith
  have hw0 : 0 ≤ W.w τ := by linarith
  obtain ⟨q, hq⟩ : ∃ q : ℝ, q = W.w τ / W.T := ⟨_, rfl⟩
  have hqT : W.w τ = q * W.T := by rw [hq]; field_simp
  have e2 : W.w τ / (2 * W.T) = q / 2 := by rw [hq]; field_simp
  have e4 : W.w τ / (4 * W.T) = q / 4 := by rw [hq]; field_simp
  have e3 : 3 / 2 * W.w τ / W.T = 3 / 2 * q := by rw [hq]; field_simp
  rw [e2, e4, e3]
  have hq20 : 20 * (N : ℝ) ≤ q := by
    have : 20 * (N : ℝ) * W.T ≤ q * W.T := by linarith
    exact le_of_mul_le_mul_right this hT0
  have hq0 : 0 ≤ q := by linarith
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = (W.T : ℝ) + W.Dd + 1 := ⟨_, rfl⟩
  have hM0 : 0 < M := by linarith
  have hM1 : M ≤ 5 / 4 * W.T := by linarith
  have hM2 : (W.T : ℝ) ≤ M := by linarith
  have hu' : ∀ i : Fin N, (W.u1 τ i : ℝ) ≤ W.u' τ i ∧ (W.u' τ i : ℝ) ≤ W.u1 τ i + 3 * N ∧
      ((i : ℕ) < W.kc → (W.u' τ i : ℝ) = W.u1 τ i) := by
    intro i
    unfold Wts.u'
    by_cases h : (i : ℕ) < W.p
    · simp [h]
    · simp only [h, if_false]
      push_cast
      exact ⟨by linarith, le_rfl, fun h' => by omega⟩
  have node : ∀ i : Fin N, W.kc ≤ (i : ℕ) → q / 2 ≤ -(W.u1 τ i : ℝ) := by
    intro i hi
    have h1 := W.node_lower_int H hd τ ((i : ℕ) + 1 - W.kc) i (by omega)
    have hn : (((i : ℕ) + 1 - W.kc : ℕ) : ℝ) ≤ N := by
      have : (i : ℕ) + 1 - W.kc ≤ N := by omega
      exact_mod_cast this
    generalize (i : ℕ) + 1 - W.kc = n at h1 hn
    have h2 : -W.u τ i - (W.c0 + 2 * (N : ℤ)) - n * ((W.T : ℤ) + W.Dd + 1) ≤
        ((W.T : ℤ) + W.Dd + 1) * (-W.u1 τ i) := by
      have := H.weightConst_nonneg
      split_ifs at h1
      · exact h1
      · have : (0 : ℤ) ≤ N := by positivity
        linarith
    have h3 : -(W.u τ i : ℝ) - (W.c0 + 2 * (N : ℝ)) - n * M ≤ M * (-(W.u1 τ i : ℝ)) := by
      rw [hM]; exact_mod_cast h2
    have h4 := (abs_le.1 (H.h3node τ i hi)).2
    have h5 : (n : ℝ) * M ≤ q / 10 * M := mul_le_mul_of_nonneg_right (by linarith) hM0.le
    have h6 : q * M ≤ q * (5 / 4 * W.T) := mul_le_mul_of_nonneg_left hM1 hq0
    have h7 : M * (q / 2) ≤ M * (-(W.u1 τ i : ℝ)) := by nlinarith
    exact le_of_mul_le_mul_left h7 hM0
  have ent : ∀ i : Fin N, M * |(W.u1 τ i : ℝ)| ≤ |(W.u τ i : ℝ)| + W.c0 + 4 * N := by
    intro i
    rw [hM]
    exact_mod_cast (GlobalTheory.MeanTop.divided_entries ι N W H hd τ i).1
  refine ⟨fun i hi => ⟨node i hi, ?_⟩, fun i l => ?_⟩
  · have h1 := node i hi
    have h2 := (hu' i).2.1
    have h3 := neg_le_abs (W.u' τ i : ℝ)
    linarith
  · have up : M * (W.u' τ i : ℝ) ≤ W.S + W.c0 + 4 * N := by
      by_cases hi : (i : ℕ) < W.kc
      · rw [(hu' i).2.2 hi]
        have h1 := ent i
        have h2 := H.h3cloud τ i hi
        have h3 : (0 : ℝ) ≤ W.u τ i := by exact_mod_cast h2.1
        rw [abs_of_nonneg h3] at h1
        have h4 := mul_le_mul_of_nonneg_left (le_abs_self (W.u1 τ i : ℝ)) hM0.le
        linarith [h2.2]
      · have h1 := node i (by omega)
        have h2 := (hu' i).2.1
        have h3 : M * (W.u' τ i : ℝ) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hM0.le (by linarith)
        linarith
    have lo : M * (-(W.u' τ l : ℝ)) ≤ W.w τ + (W.eta + W.S + N) + W.S + W.c0 + 4 * N := by
      have h1 := ent l
      have h2 : -(W.u' τ l : ℝ) ≤ |(W.u1 τ l : ℝ)| := by
        linarith [(hu' l).1, neg_le_abs (W.u1 τ l : ℝ)]
      have h3 := mul_le_mul_of_nonneg_left h2 hM0.le
      have h4 : |(W.u τ l : ℝ)| ≤ W.w τ + (W.eta + W.S + N) + W.S := by
        by_cases hl : (l : ℕ) < W.kc
        · have h2 := H.h3cloud τ l hl
          have h3 : (0 : ℝ) ≤ W.u τ l := by exact_mod_cast h2.1
          rw [abs_of_nonneg h3]
          linarith [h2.2]
        · have h5 := abs_le.1 (H.h3node τ l (by omega))
          rw [abs_le]
          constructor <;> linarith [h5.1, h5.2]
      linarith
    have h6 : q * W.T ≤ q * M := mul_le_mul_of_nonneg_left hM2 hq0
    have h7 : M * ((W.u' τ i : ℝ) - W.u' τ l) ≤ M * (3 / 2 * q) := by nlinarith
    exact le_of_mul_le_mul_left h7 hM0

end GlobalTheory.MeanTop
