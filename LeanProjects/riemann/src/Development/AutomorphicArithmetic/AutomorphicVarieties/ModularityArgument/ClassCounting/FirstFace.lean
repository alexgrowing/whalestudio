import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LemmaKOfSteps

noncomputable section

namespace UpperTheory.V.ZK

private def gz (q e : ℕ) (j : Fin (e + 1) → ZMod q) : Fin (2 * e + 1 + 1) → Cq q :=
  fun i => if (i : ℕ) % 2 = 0 then Multiplicative.ofAdd (j ⟨i / 2, by omega⟩) else Multiplicative.ofAdd 1

private theorem sum_pair {M : Type} [AddCommGroup M] (f : ℕ → M) (n : ℕ)
    (h : ∀ t < n, f (2 * t) + f (2 * t + 1) = 0) : ∑ s ∈ Finset.range (2 * n), f s = 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ, add_assoc,
      h n (by omega), ih fun t ht => h t (by omega), add_zero]

private theorem first_face (q : ℕ) [NeZero q] (e : ℕ) :
    ∑ j : Fin (e + 1) → ZMod q,
      (Finsupp.single (fun i : Fin (2 * e + 1) => gz q e j i.succ) 1 : Ch (ZMod q) (Cq q) (2 * e + 1)) = 0 := by
  rw [← (Fin.consEquiv fun _ : Fin (e + 1) => ZMod q).sum_comp, Fintype.sum_prod_type]
  have h : ∀ (a : ZMod q) (j : Fin e → ZMod q),
      (fun i : Fin (2 * e + 1) => gz q e ((Fin.consEquiv fun _ : Fin (e + 1) => ZMod q) (a, j)) i.succ) =
        fun i : Fin (2 * e + 1) => gz q e (Fin.cons 0 j) i.succ := by
    intro a j
    funext i
    unfold gz
    split_ifs with hi
    · have hi' : ((i : ℕ) + 1) % 2 = 0 := hi
      have : (⟨(i.succ : ℕ) / 2, by omega⟩ : Fin (e + 1)) = Fin.succ ⟨(i : ℕ) / 2, by omega⟩ := by
        ext; simp; omega
      rw [this]; rfl
    · rfl
  simp only [h]
  rw [Finset.sum_const, Finset.card_univ, ZMod.card, ← Nat.cast_smul_eq_nsmul (ZMod q), ZMod.natCast_self, zero_smul]

private theorem merge (q e t : ℕ) (ht : t < e + 1) (j : Fin (e + 1) → ZMod q) :
    Fin.contractNth (⟨2 * t, by omega⟩ : Fin (2 * e + 1 + 1)) (· * ·) (gz q e j) =
      Fin.contractNth (⟨2 * t + 1, by omega⟩ : Fin (2 * e + 1 + 1)) (· * ·)
        (gz q e (j + fun i : Fin (e + 1) => if (i : ℕ) = t then 1 else if (i : ℕ) = t + 1 then -1 else 0)) := by
  funext k
  rcases lt_trichotomy (k : ℕ) (2 * t) with h | h | h
  · rw [Fin.contractNth_apply_of_lt _ _ _ _ h, Fin.contractNth_apply_of_lt _ _ _ _ (by simp; omega)]
    simp only [gz, Fin.val_castSucc, Pi.add_apply]
    rw [if_neg (show ¬ (k : ℕ) / 2 = t by omega), if_neg (show ¬ (k : ℕ) / 2 = t + 1 by omega), add_zero]
  · rw [Fin.contractNth_apply_of_eq _ _ _ _ h, Fin.contractNth_apply_of_lt _ _ _ _ (by simp; omega)]
    simp only [gz, Fin.val_castSucc, Fin.val_succ, Pi.add_apply]
    rw [if_pos (show (k : ℕ) % 2 = 0 by omega), if_pos (show (k : ℕ) % 2 = 0 by omega),
      if_neg (show ¬ ((k : ℕ) + 1) % 2 = 0 by omega), if_pos (show (k : ℕ) / 2 = t by omega), ofAdd_add]
  · rw [Fin.contractNth_apply_of_gt _ _ _ _ h]
    rcases eq_or_lt_of_le (Nat.succ_le_of_lt h) with h' | h'
    · rw [Fin.contractNth_apply_of_eq _ _ _ _ h'.symm]
      simp only [gz, Fin.val_castSucc, Fin.val_succ, Pi.add_apply]
      rw [if_pos (show ((k : ℕ) + 1) % 2 = 0 by omega), if_pos (show ((k : ℕ) + 1) % 2 = 0 by omega),
        if_neg (show ¬ (k : ℕ) % 2 = 0 by omega), if_neg (show ¬ ((k : ℕ) + 1) / 2 = t by omega),
        if_pos (show ((k : ℕ) + 1) / 2 = t + 1 by omega), ← ofAdd_add]
      congr 1
      ring
    · rw [Fin.contractNth_apply_of_gt _ _ _ _ h']
      simp only [gz, Fin.val_succ, Pi.add_apply]
      have h'' : 2 * t + 1 < (k : ℕ) := h'
      by_cases h1 : ((k : ℕ) + 1) % 2 = 0
      · rw [if_neg (show ¬ ((k : ℕ) + 1) / 2 = t by omega), if_neg (show ¬ ((k : ℕ) + 1) / 2 = t + 1 by omega), add_zero]
      · rw [if_neg h1, if_neg h1]

theorem sZc : SZc := by
  intro q _ e
  have hz : zc q e = ∑ j : Fin (e + 1) → ZMod q, Finsupp.single (gz q e j) 1 := rfl
  rw [Cyc, hz, map_sum]
  simp only [bd, Finsupp.linearCombination_single, one_smul]
  rw [Finset.sum_add_distrib, first_face, zero_add, Finset.sum_comm]
  simp only [← Finset.smul_sum]
  rw [Finset.sum_fin_eq_sum_range]
  refine sum_pair _ (e + 1) fun t ht => ?_
  rw [dif_pos (show 2 * t < 2 * e + 1 + 1 by omega), dif_pos (show 2 * t + 1 < 2 * e + 1 + 1 by omega)]
  simp only [merge q e t ht]
  rw [← Equiv.sum_comp (Equiv.addRight (fun i : Fin (e + 1) => if (i : ℕ) = t then (1 : ZMod q) else
    if (i : ℕ) = t + 1 then -1 else 0)) fun j => (Finsupp.single (Fin.contractNth
      (⟨2 * t + 1, by omega⟩ : Fin (2 * e + 1 + 1)) (· * ·) (gz q e j)) 1 : Ch (ZMod q) (Cq q) (2 * e + 1))]
  simp only [Equiv.coe_addRight]
  rw [← add_smul, pow_succ (-1 : ZMod q) (2 * t + 1), mul_neg_one, add_neg_cancel, zero_smul]

end UpperTheory.V.ZK

end
