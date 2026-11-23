import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HeckePairTop

open ValuativeRel Matrix GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools

private theorem swap_lt_iff {n : ℕ} (i j x y : Fin n) (h : (j : ℕ) = i + 1)
    (h1 : ¬ (x = i ∧ y = j)) (h2 : ¬ (x = j ∧ y = i)) :
    Equiv.swap i j x < Equiv.swap i j y ↔ x < y := by
  have key : ∀ z : Fin n, (z = i ∧ Equiv.swap i j z = j) ∨ (z = j ∧ Equiv.swap i j z = i) ∨
      (z ≠ i ∧ z ≠ j ∧ Equiv.swap i j z = z) := by
    intro z
    by_cases hi : z = i
    · left; subst hi; simp
    · by_cases hj : z = j
      · right; left; subst hj; simp
      · right; right; exact ⟨hi, hj, Equiv.swap_apply_of_ne_of_ne hi hj⟩
  rcases key x with ⟨hx, ex⟩ | ⟨hx, ex⟩ | ⟨hx1, hx2, ex⟩ <;>
  rcases key y with ⟨hy, ey⟩ | ⟨hy, ey⟩ | ⟨hy1, hy2, ey⟩ <;>
  rw [ex, ey] <;> simp only [Fin.lt_iff_val_lt_val, Fin.ext_iff, ne_eq] at * <;>
  constructor <;> intro <;> omega

private theorem len_up {n : ℕ} (w : Equiv.Perm (Fin n)) (i j : Fin n) (h : (j : ℕ) = i + 1)
    (hw : w⁻¹ i < w⁻¹ j) : invLen (Equiv.swap i j * w) = invLen w + 1 := by
  have hij : i < j := by rw [Fin.lt_iff_val_lt_val]; omega
  show (Finset.univ.filter (fun p : Fin n × Fin n =>
      p.1 < p.2 ∧ (Equiv.swap i j * w) p.2 < (Equiv.swap i j * w) p.1)).card =
    (Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2 ∧ w p.2 < w p.1)).card + 1
  rw [show Finset.univ.filter (fun p : Fin n × Fin n =>
      p.1 < p.2 ∧ (Equiv.swap i j * w) p.2 < (Equiv.swap i j * w) p.1) =
    insert (w⁻¹ i, w⁻¹ j) (Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2 ∧ w p.2 < w p.1))
    from ?_]
  · apply Finset.card_insert_of_notMem
    simp [hij.le]
  · ext ⟨x, y⟩
    rw [Finset.mem_insert, Finset.mem_filter, Finset.mem_filter]
    simp only [Finset.mem_univ, true_and, Prod.mk.injEq, Equiv.Perm.mul_apply]
    by_cases hxy : x = w⁻¹ i ∧ y = w⁻¹ j
    · obtain ⟨rfl, rfl⟩ := hxy
      simp [hij]
      exact hw
    · rw [or_iff_right hxy]
      apply and_congr_right
      intro hlt
      apply swap_lt_iff i j _ _ h
      · rintro ⟨h1, h2⟩
        have e1 : y = w⁻¹ i := by rw [← h1]; simp
        have e2 : x = w⁻¹ j := by rw [← h2]; simp
        subst e1 e2
        exact absurd hlt (not_lt.mpr hw.le)
      · rintro ⟨h1, h2⟩
        exact hxy ⟨by rw [← h2]; simp, by rw [← h1]; simp⟩

private theorem len_down {n : ℕ} (w : Equiv.Perm (Fin n)) (i j : Fin n) (h : (j : ℕ) = i + 1)
    (hw : w⁻¹ j < w⁻¹ i) : invLen (Equiv.swap i j * w) + 1 = invLen w := by
  have key := len_up (Equiv.swap i j * w) i j h
    (by simpa [_root_.mul_inv_rev, Equiv.swap_inv] using hw)
  rw [← mul_assoc, Equiv.swap_mul_self, one_mul] at key
  exact key.symm

private theorem exists_desc {n : ℕ} (w : Equiv.Perm (Fin n)) (hw : w ≠ 1) :
    ∃ i j : Fin n, (j : ℕ) = i + 1 ∧ w⁻¹ j < w⁻¹ i := by
  by_contra hne
  push_neg at hne
  apply hw
  cases n with
  | zero => exact Subsingleton.elim _ _
  | succ m =>
    have hmono : StrictMono (⇑w⁻¹) := by
      rw [Fin.strictMono_iff_lt_succ]
      intro k
      refine lt_of_le_of_ne (hne _ _ (by simp)) (fun e => ?_)
      exact absurd (w⁻¹.injective e) Fin.castSucc_lt_succ.ne
    have hid : (⇑w⁻¹) = id := (hmono.range_inj strictMono_id).1 (by simp)
    rw [← inv_eq_one]
    ext x
    simp [congrFun hid x]

theorem UpperTheory.V.AlgebraTools.lenStep :
    ∀ (n : ℕ) (w : Equiv.Perm (Fin n)), (∀ (i j : Fin n), (j : ℕ) = i + 1 → (w⁻¹ i < w⁻¹ j → invLen (Equiv.swap i j * w) = invLen w + 1) ∧ (w⁻¹ j < w⁻¹ i → invLen (Equiv.swap i j * w) + 1 = invLen w)) ∧ (invLen w = 0 → w = 1) ∧ (w ≠ 1 → ∃ i j : Fin n, (j : ℕ) = i + 1 ∧ w⁻¹ j < w⁻¹ i) := by
  intro n w
  refine ⟨fun i j h => ⟨len_up w i j h, len_down w i j h⟩, fun h0 => ?_, exists_desc w⟩
  by_contra hw
  obtain ⟨i, j, h, hlt⟩ := exists_desc w hw
  have := len_down w i j h hlt
  omega
