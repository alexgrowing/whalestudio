import Mathlib
open scoped Matrix

namespace GlobalTheory

theorem ldl_gram_apply {r : ℕ} (ε : Fin r → ℝ) (b : Matrix (Fin r) (Fin r) ℂ) (a c : Fin r) :
    (bᵀ * Matrix.diagonal (fun a => ((ε a : ℝ) : ℂ)) * b.map (starRingEnd ℂ)) a c
      = ∑ j, b j a * ((ε j : ℝ) : ℂ) * starRingEnd ℂ (b j c) := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Matrix.map_apply]

theorem upperTriangular_near_diag_of_gram_near (r : ℕ) (ε : Fin r → ℝ)
    (b : Matrix (Fin r) (Fin r) ℂ) (δ : ℝ) (hε : ∀ a, ε a = 1 ∨ ε a = -1) (hδ : 0 ≤ δ)
    (hrδ : (r : ℝ) * δ ≤ 1 / 100) (htri : ∀ a c : Fin r, c < a → b a c = 0)
    (hG : ∀ a c : Fin r, ‖(bᵀ * Matrix.diagonal (fun a => ((ε a : ℝ) : ℂ)) * b.map (starRingEnd ℂ)) a c
      - Matrix.diagonal (fun a => ((ε a : ℝ) : ℂ)) a c‖ ≤ 3 * δ) :
    (∀ a : Fin r, |‖b a a‖ ^ 2 - 1| ≤ 6 * δ) ∧ ∀ a c : Fin r, a < c → ‖b a c‖ ≤ 6 * δ := by
  have hD : ∀ j, ‖((ε j : ℝ) : ℂ)‖ = 1 := fun j => by rcases hε j with h | h <;> simp [h]
  have key : ∀ a : Fin r, |‖b a a‖ ^ 2 - 1| ≤ 6 * δ ∧ ∀ c, a < c → ‖b a c‖ ≤ 6 * δ := by
    intro a
    induction a using WellFoundedLT.induction with
    | _ a ih =>
    have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Fin.pos a).ne')
    have hδ1 : δ ≤ 1 / 100 := by nlinarith

    have hR : ∀ c, a ≤ c → ‖∑ j ∈ Finset.univ.erase a, b j a * ((ε j : ℝ) : ℂ) * starRingEnd ℂ (b j c)‖
        ≤ 36 / 100 * δ := by
      intro c hac
      refine (norm_sum_le _ _).trans ?_
      have hterm : ∀ j ∈ Finset.univ.erase a,
          ‖b j a * ((ε j : ℝ) : ℂ) * starRingEnd ℂ (b j c)‖ ≤ 36 * δ ^ 2 := by
        intro j hj
        have hja : j ≠ a := Finset.ne_of_mem_erase hj
        rw [norm_mul, norm_mul, hD, Complex.norm_conj, mul_one]
        rcases lt_or_gt_of_ne hja with hlt | hgt
        · have h1 := (ih j hlt).2 a hlt
          have h2 := (ih j hlt).2 c (lt_of_lt_of_le hlt hac)
          have := mul_le_mul h1 h2 (norm_nonneg _) (by linarith)
          nlinarith
        · rw [htri j a hgt]; simp; positivity
      refine (Finset.sum_le_card_nsmul _ _ _ hterm).trans ?_
      rw [nsmul_eq_mul]
      have hc : ((Finset.univ.erase a).card : ℝ) ≤ r := by
        have := Finset.card_erase_le (s := (Finset.univ : Finset (Fin r))) (a := a)
        simp only [Finset.card_univ, Fintype.card_fin] at this
        exact_mod_cast this
      have : ((Finset.univ.erase a).card : ℝ) * (36 * δ ^ 2) ≤ r * (36 * δ ^ 2) :=
        mul_le_mul_of_nonneg_right hc (by positivity)
      nlinarith
    have hsplit : ∀ c, (bᵀ * Matrix.diagonal (fun a => ((ε a : ℝ) : ℂ)) * b.map (starRingEnd ℂ)) a c
        = b a a * ((ε a : ℝ) : ℂ) * starRingEnd ℂ (b a c)
          + ∑ j ∈ Finset.univ.erase a, b j a * ((ε j : ℝ) : ℂ) * starRingEnd ℂ (b j c) := by
      intro c
      rw [ldl_gram_apply]
      exact (Finset.add_sum_erase Finset.univ
        (fun j => b j a * ((ε j : ℝ) : ℂ) * starRingEnd ℂ (b j c)) (Finset.mem_univ a)).symm

    have hdiag : |‖b a a‖ ^ 2 - 1| ≤ 3 * δ + 36 / 100 * δ := by
      have h0 := hG a a
      rw [hsplit, Matrix.diagonal_apply_eq] at h0
      have hR0 := hR a le_rfl
      have hx : b a a * ((ε a : ℝ) : ℂ) * starRingEnd ℂ (b a a) - ((ε a : ℝ) : ℂ)
          = ((ε a : ℝ) : ℂ) * (((‖b a a‖ ^ 2 - 1 : ℝ)) : ℂ) := by
        rw [mul_right_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
      have hn : ‖b a a * ((ε a : ℝ) : ℂ) * starRingEnd ℂ (b a a) - ((ε a : ℝ) : ℂ)‖
          = |‖b a a‖ ^ 2 - 1| := by
        rw [hx, norm_mul, hD, one_mul, Complex.norm_real, Real.norm_eq_abs]
      rw [← hn]
      set R := ∑ j ∈ Finset.univ.erase a, b j a * ((ε j : ℝ) : ℂ) * starRingEnd ℂ (b j a)
      have : b a a * ((ε a : ℝ) : ℂ) * starRingEnd ℂ (b a a) - ((ε a : ℝ) : ℂ)
          = (b a a * ((ε a : ℝ) : ℂ) * starRingEnd ℂ (b a a) + R - ((ε a : ℝ) : ℂ)) - R := by ring
      rw [this]
      exact (norm_sub_le _ _).trans (add_le_add h0 hR0)
    refine ⟨by linarith, fun c hac => ?_⟩
    have h0 := hG a c
    rw [hsplit, Matrix.diagonal_apply_ne _ (ne_of_lt hac), sub_zero] at h0
    have hR0 := hR c hac.le
    have hprod : ‖b a a‖ * ‖b a c‖ ≤ 3 * δ + 36 / 100 * δ := by
      have e : ‖b a a * ((ε a : ℝ) : ℂ) * starRingEnd ℂ (b a c)‖ = ‖b a a‖ * ‖b a c‖ := by
        rw [norm_mul, norm_mul, hD, Complex.norm_conj, mul_one]
      rw [← e]
      set R := ∑ j ∈ Finset.univ.erase a, b j a * ((ε j : ℝ) : ℂ) * starRingEnd ℂ (b j c)
      have : b a a * ((ε a : ℝ) : ℂ) * starRingEnd ℂ (b a c)
          = (b a a * ((ε a : ℝ) : ℂ) * starRingEnd ℂ (b a c) + R) - R := by ring
      rw [this]
      exact (norm_sub_le _ _).trans (add_le_add h0 hR0)
    have hsq : 9 / 10 ≤ ‖b a a‖ := by
      have h1 := (abs_le.mp hdiag).1
      nlinarith [norm_nonneg (b a a)]
    have hy := norm_nonneg (b a c)
    nlinarith
  exact ⟨fun a => (key a).1, fun a c h => (key a).2 c h⟩

end GlobalTheory
