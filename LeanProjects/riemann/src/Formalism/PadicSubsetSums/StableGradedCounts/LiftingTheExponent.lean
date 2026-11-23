import Formalism.PadicSubsetSums.CentralIdempotents.WindowSums

namespace Formalism.IrreducibleCountingLemmas.WindowSums

theorem sum_one_add_val (l : ℕ) [Fact l.Prime] (n : ℕ) :
    ∑ i ∈ Finset.range n, (1 + padicValNat l (i + 1)) = n + padicValNat l n.factorial := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, Nat.factorial_succ,
      padicValNat.mul (Nat.succ_ne_zero n) (Nat.factorial_ne_zero n)]
    simp only [Nat.succ_eq_add_one]
    omega

theorem two_mul_val_factorial_le (l : ℕ) [hl : Fact l.Prime] (h2 : l ≠ 2) (n : ℕ) :
    2 * padicValNat l n.factorial ≤ n := by
  have h3 : 3 ≤ l := by have := hl.out.two_le; omega
  have key := sub_one_mul_padicValNat_factorial (p := l) n
  have hle : (l - 1) * padicValNat l n.factorial ≤ n := by rw [key]; exact Nat.sub_le _ _
  have h2le : 2 * padicValNat l n.factorial ≤ (l - 1) * padicValNat l n.factorial :=
    Nat.mul_le_mul_right _ (by omega)
  omega

private theorem padicValInt_neg_natCast_add_one (l i : ℕ) :
    padicValInt l (-((i : ℤ) + 1)) = padicValNat l (i + 1) := by
  simp only [padicValInt]
  rw [show (-((i : ℤ) + 1)).natAbs = i + 1 by omega]

private theorem padicValInt_natCast_add_one (l i : ℕ) :
    padicValInt l ((i : ℤ) + 1) = padicValNat l (i + 1) := by
  simp only [padicValInt]
  rw [show ((i : ℤ) + 1).natAbs = i + 1 by omega]

theorem valuationSumBound : LiftExp := by
  intro l h J hl hl2 hJ h0
  have : Fact l.Prime := ⟨hl⟩
  set f : ℤ → ℕ := fun j => 1 + padicValInt l j with hf
  set A : Finset ℤ := (Finset.range h).image (fun i : ℕ => -((i : ℤ) + 1)) with hA
  set B : Finset ℤ := (Finset.range (2 * h)).image (fun i : ℕ => (i : ℤ) + 1) with hB
  have hsub : J ⊆ A ∪ B := by
    intro j hj
    have hm := Finset.mem_Icc.mp (hJ hj)
    have hj0 : j ≠ 0 := fun e => h0 (e ▸ hj)
    rw [Finset.mem_union, hA, hB, Finset.mem_image, Finset.mem_image]
    rcases lt_or_gt_of_ne hj0 with hneg | hpos
    · left
      exact ⟨(-j - 1).toNat, by rw [Finset.mem_range]; omega, by omega⟩
    · right
      exact ⟨(j - 1).toNat, by rw [Finset.mem_range]; omega, by omega⟩
  have hA_sum : ∑ j ∈ A, f j = h + padicValNat l h.factorial := by
    rw [hA, Finset.sum_image (fun x _ y _ e => by simpa using e)]
    rw [← sum_one_add_val l h]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [hf, padicValInt_neg_natCast_add_one]
  have hB_sum : ∑ j ∈ B, f j = 2 * h + padicValNat l (2 * h).factorial := by
    rw [hB, Finset.sum_image (fun x _ y _ e => by simpa using e)]
    rw [← sum_one_add_val l (2 * h)]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [hf, padicValInt_natCast_add_one]
  have hJle : ∑ j ∈ J, f j ≤ ∑ j ∈ A ∪ B, f j := Finset.sum_le_sum_of_subset hsub
  have hU := Finset.sum_union_inter (s₁ := A) (s₂ := B) (f := f)
  have e1 := two_mul_val_factorial_le l hl2 (2 * (2 * h))
  have e2 := two_mul_val_factorial_le l hl2 h
  have e3 := two_mul_val_factorial_le l hl2 (2 * h)
  have hJ' : ∑ j ∈ J, (1 + padicValInt l j) = ∑ j ∈ J, f j := rfl
  rw [hJ']
  omega

end Formalism.IrreducibleCountingLemmas.WindowSums
