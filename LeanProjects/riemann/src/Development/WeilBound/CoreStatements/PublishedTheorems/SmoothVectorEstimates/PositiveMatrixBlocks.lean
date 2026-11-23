import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.MirabolicColumnBlock

noncomputable section

open MeasureTheory Matrix GlobalTheory.CuspGeneric Topology
open scoped ContDiff

namespace PositivityTheory.jumpWindows

namespace PositiveMatrixBlocks

variable {R : Type} [CommRing R] {a : ℕ}

theorem posM_col (m : ℕ) (y : UnipotentBlockColumnIndex a m m → R) (i k : Fin a) :
    posM (Subtype.val : UnipotentBlockColumnIndex a m m → Fin a × Fin a) y i k =
      if hik : (i : ℕ) < m ∧ (k : ℕ) = m then y ⟨(i, k), hik.1, hik.2.ge, hik.2.le⟩ else 0 := by
  rw [posM, Matrix.sum_apply]
  split_ifs with hik
  · rw [Finset.sum_eq_single ⟨(i, k), hik.1, hik.2.ge, hik.2.le⟩]
    · simp
    · intro b _ hb
      rw [Matrix.single_apply, if_neg]
      rintro ⟨h1, h2⟩
      exact hb (Subtype.ext (Prod.ext h1 h2))
    · intro h
      exact absurd (Finset.mem_univ _) h
  · refine Finset.sum_eq_zero fun t _ => ?_
    rw [Matrix.single_apply, if_neg]
    rintro ⟨h1, h2⟩
    apply hik
    have := t.2
    rw [← h1, ← h2]
    omega

theorem posM_mul_apply {ι : Type} [Fintype ι] (p : ι → Fin a × Fin a) (y : ι → R)
    (M : Matrix (Fin a) (Fin a) R) (i k : Fin a) :
    (posM p y * M) i k = ∑ s, if (p s).1 = i then y s * M (p s).2 k else 0 := by
  simp only [posM, Matrix.sum_mul, Matrix.sum_apply]
  refine Finset.sum_congr rfl fun s _ => ?_
  by_cases h : (p s).1 = i
  · subst h
    simp [Matrix.single_mul_apply_same]
  · rw [if_neg h, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [Matrix.single_apply, if_neg (fun e => h e.1), zero_mul]

theorem mul_posM_apply {ι : Type} [Fintype ι] (p : ι → Fin a × Fin a) (y : ι → R)
    (M : Matrix (Fin a) (Fin a) R) (i k : Fin a) :
    (M * posM p y) i k = ∑ s, if (p s).2 = k then M i (p s).1 * y s else 0 := by
  simp only [posM, Matrix.mul_sum, Matrix.sum_apply]
  refine Finset.sum_congr rfl fun s _ => ?_
  by_cases h : (p s).2 = k
  · subst h
    simp [Matrix.mul_single_apply_same]
  · rw [if_neg h, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [Matrix.single_apply, if_neg (fun e => h e.2), mul_zero]

theorem posM_mul_row (m : ℕ) (y : UnipotentBlockColumnIndex a m m → R) (M : Matrix (Fin a) (Fin a) R)
    (hM : ∀ j k : Fin a, (j : ℕ) = m → M j k = (1 : Matrix (Fin a) (Fin a) R) j k) :
    posM (Subtype.val : UnipotentBlockColumnIndex a m m → Fin a × Fin a) y * M = posM Subtype.val y := by
  ext i k
  have e := posM_mul_apply (Subtype.val : UnipotentBlockColumnIndex a m m → Fin a × Fin a) y 1 i k
  rw [Matrix.mul_one] at e
  rw [e, posM_mul_apply]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [hM s.1.2 k (by have := s.2; omega)]

theorem mul_posM_blk (m : ℕ) (y : UnipotentBlockColumnIndex a m m → R) (h : GL (Fin a) R) (hB : GlobalTheory m h) :
    h.val * posM (Subtype.val : UnipotentBlockColumnIndex a m m → Fin a × Fin a) y =
      posM Subtype.val (fun t : UnipotentBlockColumnIndex a m m => ∑ s, h.val t.1.1 s.1.1 * y s) := by
  ext i k
  rw [mul_posM_apply, posM_col]
  split_ifs with hc
  · refine Finset.sum_congr rfl fun s _ => ?_
    rw [if_pos (Fin.ext (by have := s.2; omega))]
  · refine Finset.sum_eq_zero fun s _ => ?_
    split_ifs with hs
    · have h2 := s.2
      have hk : (k : ℕ) = m := by rw [← hs]; omega
      have hi : m ≤ (i : ℕ) := by
        by_contra hh
        exact hc ⟨by omega, hk⟩
      rw [hB i s.1.1 (Or.inl hi), Matrix.one_apply_ne, zero_mul]
      intro e
      rw [← e] at h2
      omega
    · rfl

end PositiveMatrixBlocks

theorem positive_matrix_block_product : MirabolicColumnBlock := by
  intro R _ a m
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro γ hγ
    refine ⟨fun t => γ.val t.1.1 t.1.2, blkU (-(fun t : UnipotentBlockColumnIndex a m m => γ.val t.1.1 t.1.2)) * γ, ?_, ?_⟩
    · intro i k hik
      show ((1 + posM Subtype.val (-(fun t : UnipotentBlockColumnIndex a m m => γ.val t.1.1 t.1.2))) * γ.val) i k = _
      rw [add_mul, one_mul, PositiveMatrixBlocks.posM_mul_row m _ γ.val (fun j k hj => hγ j k (Or.inl hj.ge)),
        Matrix.add_apply, PositiveMatrixBlocks.posM_col]
      split_ifs with hc
      · rcases hik with hi | _
        · omega
        · rw [Matrix.one_apply_ne (fun e => by rw [e] at hc; omega)]
          simp
      · rw [add_zero]
        exact hγ i k (by omega)
    · show γ = blkU _ * (blkU _ * γ)
      rw [← mul_assoc]
      unfold blkU
      rw [← posU_add, add_neg_cancel, posU_zero, one_mul]
  · intro γ hγ
    apply Units.ext
    ext i k
    exact hγ i k (Or.inl (Nat.zero_le _))
  · intro i k _
    rfl
  · intro i k _
    rfl
  · intro γ γ' hγ hγ' i k hik
    show (γ.val * γ'.val) i k = _
    rw [Matrix.mul_apply]
    rcases hik with hi | hk
    · calc ∑ j, γ.val i j * γ'.val j k = ∑ j, (1 : Matrix (Fin a) (Fin a) R) i j * γ'.val j k :=
            Finset.sum_congr rfl fun j _ => by rw [hγ i j (Or.inl hi)]
        _ = ((1 : Matrix (Fin a) (Fin a) R) * γ'.val) i k := Matrix.mul_apply.symm
        _ = _ := by rw [Matrix.one_mul]; exact hγ' i k (Or.inl hi)
    · calc ∑ j, γ.val i j * γ'.val j k = ∑ j, γ.val i j * (1 : Matrix (Fin a) (Fin a) R) j k :=
            Finset.sum_congr rfl fun j _ => by rw [hγ' j k (Or.inr hk)]
        _ = (γ.val * (1 : Matrix (Fin a) (Fin a) R)) i k := Matrix.mul_apply.symm
        _ = _ := by rw [Matrix.mul_one]; exact hγ i k (Or.inr hk)
  · intro k y hkm i l hil
    show (1 + posM Subtype.val y) i l = _
    rw [Matrix.add_apply, posM, Matrix.sum_apply, Finset.sum_eq_zero, add_zero]
    intro t _
    rw [Matrix.single_apply, if_neg]
    rintro ⟨e1, e2⟩
    have := t.2
    rw [← e1, ← e2] at hil
    omega
  · intro k γ hkm hγ i l hil
    exact hγ i l (by omega)
  · intro h hB y
    refine ⟨fun t => ∑ s, h.val t.1.1 s.1.1 * y s, ?_, fun t => rfl⟩
    apply Units.ext
    show h.val * (1 + posM Subtype.val y) = (1 + posM Subtype.val _) * h.val
    rw [mul_add, add_mul, mul_one, one_mul,
      PositiveMatrixBlocks.posM_mul_row m _ h.val (fun j k hj => hB j k (Or.inl hj.ge)), PositiveMatrixBlocks.mul_posM_blk m y h hB]

end PositivityTheory.jumpWindows

end
