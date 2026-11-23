import Mathlib

open Polynomial Matrix

namespace UpperTheory.V.Pr.T

private def IwReach {K : Type} [Field K] (V : ValuationSubring K) {n : ℕ} (Y Z : Matrix (Fin n) (Fin n) K) : Prop :=
  ∃ k : GL (Fin n) V, ((k : Matrix (Fin n) (Fin n) V).map V.subtype) * Y = Z

section
variable {K : Type} [Field K] (V : ValuationSubring K) {n : ℕ}

private theorem iw_refl (Y : Matrix (Fin n) (Fin n) K) : IwReach V Y Y := by
  refine ⟨1, ?_⟩
  simp

private theorem iw_trans {X Y Z : Matrix (Fin n) (Fin n) K} (h1 : IwReach V X Y) (h2 : IwReach V Y Z) :
    IwReach V X Z := by
  obtain ⟨k1, rfl⟩ := h1
  obtain ⟨k2, rfl⟩ := h2
  exact ⟨k2 * k1, by rw [Units.val_mul, Matrix.map_mul, Matrix.mul_assoc]⟩

private theorem iw_perm (Y : Matrix (Fin n) (Fin n) K) (σ : Equiv.Perm (Fin n)) :
    IwReach V Y (Y.submatrix σ id) := by
  classical
  refine ⟨⟨σ.toPEquiv.toMatrix, σ.symm.toPEquiv.toMatrix, ?_, ?_⟩, ?_⟩
  · rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans, Equiv.self_trans_symm,
      Equiv.toPEquiv_refl, PEquiv.toMatrix_refl]
  · rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans, Equiv.symm_trans_self,
      Equiv.toPEquiv_refl, PEquiv.toMatrix_refl]
  · show (σ.toPEquiv.toMatrix : Matrix (Fin n) (Fin n) V).map V.subtype * Y = _
    rw [PEquiv.map_toMatrix, PEquiv.toMatrix_toPEquiv_mul]

private theorem iw_clear (Y : Matrix (Fin n) (Fin n) K) (c : Fin n) (a : Fin n → V) (ha : a c = 0) :
    IwReach V Y (Matrix.of fun i j => Y i j - (a i : K) * Y c j) := by
  classical
  let A : Matrix (Fin n) (Fin n) V := Matrix.of fun i j => if j = c then a i else 0
  have hA2 : A * A = 0 := by
    ext i j
    simp [A, Matrix.mul_apply, ha]
  refine ⟨⟨1 - A, 1 + A, by simp [sub_mul, mul_add, hA2], by simp [add_mul, mul_sub, hA2]⟩, ?_⟩
  ext i j
  simp [A, Matrix.mul_apply, Matrix.one_apply, sub_mul, Finset.sum_sub_distrib]
  simp only [apply_ite (fun x : V => (x : K)), ZeroMemClass.coe_zero, OneMemClass.coe_one, ite_mul,
    one_mul, zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]

private theorem iw_step (Y : Matrix (Fin n) (Fin n) K) (c : Fin n)
    (hY : ∀ i j : Fin n, j < c → j < i → Y i j = 0) :
    ∃ Z, IwReach V Y Z ∧ ∀ i j : Fin n, j ≤ c → j < i → Z i j = 0 := by
  classical
  obtain ⟨p, hp, hpmax⟩ := Finset.exists_max_image (Finset.univ.filter fun i => c ≤ i)
    (fun i => V.valuation (Y i c)) ⟨c, by simp⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp hpmax
  set Y1 := Y.submatrix (Equiv.swap c p) id with hY1
  have r1 : IwReach V Y Y1 := iw_perm V Y _
  have hY1c : ∀ i j : Fin n, j < c → j < i → Y1 i j = 0 := by
    intro i j hjc hji
    simp only [hY1, Matrix.submatrix_apply, id]
    apply hY _ _ hjc
    rcases eq_or_ne i c with rfl | hic
    · rw [Equiv.swap_apply_left]
      exact lt_of_lt_of_le hjc hp
    rcases eq_or_ne i p with rfl | hip
    · rw [Equiv.swap_apply_right]
      exact hjc
    · rw [Equiv.swap_apply_of_ne_of_ne hic hip]
      exact hji
  have hmax1 : ∀ i, c ≤ i → V.valuation (Y1 i c) ≤ V.valuation (Y1 c c) := by
    intro i hi
    simp only [hY1, Matrix.submatrix_apply, id, Equiv.swap_apply_left]
    apply hpmax
    rcases eq_or_ne i c with rfl | hic
    · rw [Equiv.swap_apply_left]
      exact hp
    rcases eq_or_ne i p with rfl | hip
    · rw [Equiv.swap_apply_right]
    · rw [Equiv.swap_apply_of_ne_of_ne hic hip]
      exact hi
  by_cases h0 : Y1 c c = 0
  · refine ⟨Y1, r1, fun i j hjc hji => ?_⟩
    rcases lt_or_eq_of_le hjc with hlt | heq
    · exact hY1c i j hlt hji
    · rw [heq] at hji ⊢
      have h1 := hmax1 i hji.le
      rw [h0, map_zero] at h1
      exact (Valuation.zero_iff _).1 (le_antisymm h1 zero_le')
  · have hmem : ∀ i, c ≤ i → Y1 i c / Y1 c c ∈ V := by
      intro i hi
      rw [← V.valuation_le_one_iff, map_div₀, div_le_one₀ ((Valuation.pos_iff _).2 h0)]
      exact hmax1 i hi
    let a : Fin n → V := fun i => if h : c < i then ⟨Y1 i c / Y1 c c, hmem i h.le⟩ else 0
    have ha : a c = 0 := by simp [a]
    refine ⟨_, iw_trans V r1 (iw_clear V Y1 c a ha), fun i j hjc hji => ?_⟩
    simp only [Matrix.of_apply]
    rcases lt_or_eq_of_le hjc with hlt | heq
    · rw [hY1c i j hlt hji, hY1c c j hlt hlt, mul_zero, sub_zero]
    · rw [heq] at hji ⊢
      simp only [a, dif_pos hji]
      show Y1 i c - Y1 i c / Y1 c c * Y1 c c = 0
      rw [div_mul_cancel₀ _ h0, sub_self]

private theorem iw_ind (Y : Matrix (Fin n) (Fin n) K) (m : ℕ) :
    ∃ Z, IwReach V Y Z ∧ ∀ i j : Fin n, (j : ℕ) < m → j < i → Z i j = 0 := by
  induction m with
  | zero => exact ⟨Y, iw_refl V Y, fun _ _ h => absurd h (Nat.not_lt_zero _)⟩
  | succ m ih =>
    obtain ⟨Z, hZ, h⟩ := ih
    by_cases hm : m < n
    · obtain ⟨Z', hZ', h'⟩ := iw_step V Z ⟨m, hm⟩ (fun i j hj hi => h i j hj hi)
      exact ⟨Z', iw_trans V hZ hZ', fun i j hj hi => h' i j (Nat.lt_succ_iff.1 hj) hi⟩
    · exact ⟨Z, hZ, fun i j _ hi => h i j (by have := j.2; omega) hi⟩

end

end UpperTheory.V.Pr.T

theorem UpperTheory.V.Pr.T.iwasawaVal :
    ∀ {K : Type} [Field K] (V : ValuationSubring K) (n : ℕ) (Y : Matrix (Fin n) (Fin n) K),
      ∃ k : GL (Fin n) V, (((k : Matrix (Fin n) (Fin n) V).map V.subtype) * Y).BlockTriangular id := by
  intro K _ V n Y
  obtain ⟨Z, ⟨k, hk⟩, hZ⟩ := iw_ind V Y n
  refine ⟨k, ?_⟩
  rw [hk]
  intro i j hij
  exact hZ i j j.isLt hij
