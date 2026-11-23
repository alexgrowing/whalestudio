import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.DecMomentsA

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

lemma dm_swap4 (F : Fin n → Fin n → Fin n → Fin n → ℂ) :
    ∑ k, ∑ l, ∑ a, ∑ b, F k l a b = ∑ a, ∑ b, ∑ k, ∑ l, F k l a b := by
  calc ∑ k, ∑ l, ∑ a, ∑ b, F k l a b = ∑ k, ∑ a, ∑ l, ∑ b, F k l a b :=
        Finset.sum_congr rfl (fun k _ => Finset.sum_comm)
    _ = ∑ a, ∑ k, ∑ l, ∑ b, F k l a b := Finset.sum_comm
    _ = ∑ a, ∑ k, ∑ b, ∑ l, F k l a b :=
        Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun k _ => Finset.sum_comm))
    _ = ∑ a, ∑ b, ∑ k, ∑ l, F k l a b := Finset.sum_congr rfl (fun a _ => Finset.sum_comm)

variable {U Y : Matrix (Fin n) (Fin n) ℂ} {y : Fin n → ℝ}

lemma dm_Ye (hY : Y = U * Matrix.diagonal (fun j => (y j : ℂ)) * Uᴴ) (a b : Fin n) :
    Y a b = ∑ j, U a j * (y j : ℂ) * star (U b j) := by
  rw [hY, dm_entry]

lemma dm_herm (hY : Y = U * Matrix.diagonal (fun j => (y j : ℂ)) * Uᴴ) (a b : Fin n) :
    Y b a = star (Y a b) := by
  rw [dm_Ye hY, dm_Ye hY, star_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [star_mul', star_star]
  simp only [Complex.star_def, Complex.conj_ofReal]
  ring

lemma trace_diag_conj_eq (hY : Y = U * Matrix.diagonal (fun j => (y j : ℂ)) * Uᴴ) (i : ℕ) :
    ∑ k, (y k : ℂ) * dmK U i k k = ∑ a, dmChi i a * Y a a := by
  simp only [dmK, Finset.mul_sum, dm_Ye hY]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun k _ => ?_
  ring

lemma trace_sq_diag_conj_eq (hY : Y = U * Matrix.diagonal (fun j => (y j : ℂ)) * Uᴴ) (i : ℕ) :
    ∑ k, ∑ l, (y k : ℂ) * (y l : ℂ) * (dmK U i k l * dmK U i l k) =
      ∑ a, ∑ b, dmChi i a * dmChi i b * (Y b a * Y a b) := by
  have hL : ∀ k l, (y k : ℂ) * (y l : ℂ) * (dmK U i k l * dmK U i l k) =
      ∑ a, ∑ b, (y k : ℂ) * (y l : ℂ) *
        ((dmChi i a * (star (U a k) * U a l)) * (dmChi i b * (star (U b l) * U b k))) := by
    intro k l
    rw [dmK, dmK, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
  have hR : ∀ a b, dmChi i a * dmChi i b * (Y b a * Y a b) =
      ∑ k, ∑ l, dmChi i a * dmChi i b *
        ((U b k * (y k : ℂ) * star (U a k)) * (U a l * (y l : ℂ) * star (U b l))) := by
    intro a b
    rw [dm_Ye hY b a, dm_Ye hY a b, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
  simp only [hL, hR]
  rw [dm_swap4]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

lemma trace_pow_two_diag_conj (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) (hY : Y = U * Matrix.diagonal (fun j => (y j : ℂ)) * Uᴴ)
    (i : ℕ) :
    ∑ k, (y k : ℂ) ^ 2 * dmK U i k k = ∑ a, dmChi i a * ∑ b, Y a b * Y b a := by
  have hYY : Y * Y = U * Matrix.diagonal (fun j => (y j : ℂ) ^ 2) * Uᴴ := by
    rw [hY]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Uᴴ U, dm_UhU hU, Matrix.one_mul, ← Matrix.mul_assoc (Matrix.diagonal _),
      Matrix.diagonal_mul_diagonal]
    simp only [sq]
  have hrow : ∀ a, ∑ b, Y a b * Y b a = ∑ k, U a k * (y k : ℂ) ^ 2 * star (U a k) := by
    intro a
    rw [← Matrix.mul_apply, hYY, dm_entry]
  simp only [hrow, dmK, Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun k _ => ?_
  ring

lemma dm_hs (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) (hY : Y = U * Matrix.diagonal (fun j => (y j : ℂ)) * Uᴴ) :
    hs Y = ∑ k, y k ^ 2 := by
  apply Complex.ofReal_injective
  have h3 := trace_pow_two_diag_conj hU hY n
  have hchi : ∀ a : Fin n, dmChi n a = 1 := by intro a; simp [dmChi, a.isLt]
  have hKn : ∀ k, dmK U n k k = 1 := by
    intro k
    have h := congrFun (congrFun (dm_UhU hU) k) k
    rw [Matrix.mul_apply, Matrix.one_apply_eq] at h
    simp only [dmK, hchi, one_mul]
    rw [← h]
    rfl
  simp only [hchi, hKn, one_mul, mul_one] at h3
  rw [hs, Complex.ofReal_sum, Complex.ofReal_sum]
  simp only [Complex.ofReal_sum, Complex.ofReal_pow, h3]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [← Complex.ofReal_pow, dm_normsq, ← dm_herm hY a b]

lemma dm_S (J : Finset (Fin n)) : ((∑ j ∈ J, y j : ℝ) : ℂ) = ∑ k, dmInd J k * (y k : ℂ) := by
  push_cast
  unfold dmInd
  simp only [ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_mem, Finset.univ_inter]

lemma dm_mean (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) (hY : Y = U * Matrix.diagonal (fun j => (y j : ℂ)) * Uᴴ)
    (hd : ∀ a, Y a a = 0) {i : ℕ} (hi : i ≤ n) :
    ∑ J : {J : Finset (Fin n) // J.card = i}, ((dmW U hi J : ℝ) : ℂ) * ((∑ j ∈ J.1, y j : ℝ) : ℂ) = 0 := by
  simp only [dm_S, Finset.mul_sum]
  rw [Finset.sum_comm]
  have h : ∀ k, ∑ J : {J : Finset (Fin n) // J.card = i}, ((dmW U hi J : ℝ) : ℂ) * (dmInd J.1 k * (y k : ℂ)) =
      (y k : ℂ) * dmK U i k k := by
    intro k
    rw [← sum_minorWeights_indicator hU hi k, Finset.mul_sum]
    refine Finset.sum_congr rfl fun J _ => ?_
    ring
  simp only [h, trace_diag_conj_eq hY, hd, mul_zero, Finset.sum_const_zero]

lemma dm_var (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) (hY : Y = U * Matrix.diagonal (fun j => (y j : ℂ)) * Uᴴ)
    (hd : ∀ a, Y a a = 0) {i : ℕ} (hi : i ≤ n) :
    ∑ J : {J : Finset (Fin n) // J.card = i}, ((dmW U hi J : ℝ) : ℂ) * ((∑ j ∈ J.1, y j : ℝ) : ℂ) ^ 2 =
      ∑ a, ∑ b, dmChi i a * (1 - dmChi i b) * (Y a b * Y b a) := by
  calc ∑ J : {J : Finset (Fin n) // J.card = i}, ((dmW U hi J : ℝ) : ℂ) * ((∑ j ∈ J.1, y j : ℝ) : ℂ) ^ 2
        = ∑ J : {J : Finset (Fin n) // J.card = i}, ∑ k, ∑ l,
            ((dmW U hi J : ℝ) : ℂ) * (dmInd J.1 k * dmInd J.1 l) * ((y k : ℂ) * (y l : ℂ)) := by
          refine Finset.sum_congr rfl fun J _ => ?_
          rw [dm_S, sq, Finset.sum_mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun l _ => ?_
          ring
    _ = ∑ k, ∑ J : {J : Finset (Fin n) // J.card = i}, ∑ l,
            ((dmW U hi J : ℝ) : ℂ) * (dmInd J.1 k * dmInd J.1 l) * ((y k : ℂ) * (y l : ℂ)) :=
          Finset.sum_comm
    _ = ∑ k, ∑ l, ∑ J : {J : Finset (Fin n) // J.card = i},
            ((dmW U hi J : ℝ) : ℂ) * (dmInd J.1 k * dmInd J.1 l) * ((y k : ℂ) * (y l : ℂ)) :=
          Finset.sum_congr rfl fun k _ => Finset.sum_comm
    _ = ∑ k, ∑ l, (y k : ℂ) * (y l : ℂ) * (dmK U i k k * dmK U i l l - dmK U i k l * dmK U i l k +
            if k = l then dmK U i k k else 0) := by
          refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
          rw [← dm_m hU hi k l, Finset.mul_sum]
          refine Finset.sum_congr rfl fun J _ => ?_
          ring
    _ = (∑ k, (y k : ℂ) * dmK U i k k) * (∑ l, (y l : ℂ) * dmK U i l l) -
          ∑ k, ∑ l, (y k : ℂ) * (y l : ℂ) * (dmK U i k l * dmK U i l k) +
          ∑ k, (y k : ℂ) ^ 2 * dmK U i k k := by
          have hk : ∀ k, ∑ l, (y k : ℂ) * (y l : ℂ) * (dmK U i k k * dmK U i l l - dmK U i k l * dmK U i l k +
              if k = l then dmK U i k k else 0) =
              ∑ l, ((y k : ℂ) * dmK U i k k) * ((y l : ℂ) * dmK U i l l) -
              ∑ l, (y k : ℂ) * (y l : ℂ) * (dmK U i k l * dmK U i l k) + (y k : ℂ) ^ 2 * dmK U i k k := by
            intro k
            have e : ∀ l, (y k : ℂ) * (y l : ℂ) * (dmK U i k k * dmK U i l l - dmK U i k l * dmK U i l k +
                if k = l then dmK U i k k else 0) =
                ((y k : ℂ) * dmK U i k k) * ((y l : ℂ) * dmK U i l l) -
                (y k : ℂ) * (y l : ℂ) * (dmK U i k l * dmK U i l k) +
                if k = l then (y k : ℂ) ^ 2 * dmK U i k k else 0 := by
              intro l
              split_ifs with h
              · subst h; ring
              · ring
            rw [Finset.sum_congr rfl fun l _ => e l, Finset.sum_add_distrib, Finset.sum_sub_distrib,
              Finset.sum_ite_eq]
            simp only [Finset.mem_univ, if_true]
          rw [Finset.sum_congr rfl fun k _ => hk k, Finset.sum_add_distrib, Finset.sum_sub_distrib,
            Finset.sum_mul_sum]
    _ = ∑ a, ∑ b, dmChi i a * (1 - dmChi i b) * (Y a b * Y b a) := by
          rw [trace_diag_conj_eq hY, trace_sq_diag_conj_eq hY, trace_pow_two_diag_conj hU hY]
          simp only [hd, mul_zero, Finset.sum_const_zero, zero_sub]
          have e : ∀ a b, dmChi i a * (1 - dmChi i b) * (Y a b * Y b a) =
              dmChi i a * (Y a b * Y b a) - dmChi i a * dmChi i b * (Y b a * Y a b) := by
            intro a b; ring
          simp only [e, Finset.sum_sub_distrib, ← Finset.mul_sum]
          ring

lemma dm_rhs (hY : Y = U * Matrix.diagonal (fun j => (y j : ℂ)) * Uᴴ) (i : ℕ) :
    ∑ a, ∑ b, dmChi i a * (1 - dmChi i b) * (Y a b * Y b a) =
      ((∑ a : Fin n, ∑ b : Fin n, if (b : ℕ) < i ∧ i ≤ (a : ℕ) then ‖Y a b‖ ^ 2 else 0 : ℝ) : ℂ) := by
  conv_lhs => rw [Finset.sum_comm]
  rw [Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  by_cases hb : (b : ℕ) < i <;> by_cases ha : (a : ℕ) < i
  · rw [if_neg (fun h => absurd h.2 (not_le.mpr ha))]; simp [dmChi, hb, ha]
  · rw [if_pos ⟨hb, not_lt.mp ha⟩, dm_normsq, ← dm_herm hY a b]
    simp only [dmChi, if_pos hb, if_neg ha]; ring
  · rw [if_neg (fun h => hb h.1)]; simp [dmChi, hb, ha]
  · rw [if_neg (fun h => hb h.1)]; simp [dmChi, hb, ha]

end ReciprocityTheory.ChartRestriction.DS.S7
