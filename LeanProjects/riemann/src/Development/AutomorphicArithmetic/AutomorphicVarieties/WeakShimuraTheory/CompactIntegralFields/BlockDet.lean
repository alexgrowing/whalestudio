import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RedIdeal

open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

section SlopeTestRemainingChoices

variable {R : Type} [CommRing R]

private theorem bd_up_mul {Y Z : M4 R} (hY : IsUp Y) (hZ : IsUp Z) : IsUp (Y * Z) := by
  intro i j hij
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases h : k < i
  · rw [hY i k h, zero_mul]
  · rw [hZ k j (lt_of_lt_of_le hij (not_lt.mp h)), mul_zero]

private theorem bd_up_diag {Y Z : M4 R} (hY : IsUp Y) (hZ : IsUp Z) (i : Fin 4) : (Y * Z) i i = Y i i * Z i i := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_single i (fun k _ hk => ?_) (by simp)
  rcases lt_or_gt_of_ne hk with h | h
  · rw [hY i k h, zero_mul]
  · rw [hZ k i h, mul_zero]

private theorem bd_conj_mul {u v : M4 R} (h : u * v = 1) (Y Z : M4 R) :
    v * (Y * Z) * u = (v * Y * u) * (v * Z * u) := by
  have : (v * Y * u) * (v * Z * u) = v * Y * (u * v) * Z * u := by simp only [Matrix.mul_assoc]
  rw [this, h]; simp only [Matrix.mul_assoc, Matrix.one_mul]

private theorem bd_trace {u v : M4 R} (h : u * v = 1) (Y : M4 R) : (v * Y * u).trace = Y.trace := by
  rw [Matrix.trace_mul_cycle, h, Matrix.one_mul]

private theorem bd_key {u v N X : M4 R} (h : u * v = 1) (hN : IsUp (v * N * u)) (hX : IsUp (v * X * u)) :
    (N * X).trace ^ 2 - ((N * X) * (N * X)).trace =
      (∑ i, (v * N * u) i i * (v * X * u) i i) ^ 2 - ∑ i, ((v * N * u) i i * (v * X * u) i i) ^ 2 := by
  have hU := bd_up_mul hN hX
  rw [← bd_trace h (N * X), ← bd_trace h ((N * X) * (N * X)), bd_conj_mul h (N * X), bd_conj_mul h N X]
  simp only [Matrix.trace, Matrix.diag_apply, bd_up_diag hU hU, bd_up_diag hN hX, sq]

private theorem bd_poly {u v S : M4 R} (h : u * v = 1) (h' : v * u = 1) (b c : R) :
    v * (S * S - b • S + c • (1 : M4 R)) * u = (v * S * u) * (v * S * u) - b • (v * S * u) + c • (1 : M4 R) := by
  rw [← bd_conj_mul h]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_one, h']

private theorem bd_poly_up {T : M4 R} (hT : IsUp T) (b c : R) : IsUp (T * T - b • T + c • (1 : M4 R)) := by
  intro i j hij
  simp [bd_up_mul hT hT i j hij, hT i j hij, Matrix.one_apply_ne hij.ne']

private theorem bd_poly_diag {T : M4 R} (hT : IsUp T) (b c : R) (i : Fin 4) :
    (T * T - b • T + c • (1 : M4 R)) i i = T i i * T i i - b * T i i + c := by
  simp [bd_up_diag hT hT]

private theorem bd_notMem (m : Ideal R) [hm : m.IsPrime] {t x p q p' q' r s : R} (ht : t - x ∈ m) (hp : p' - p ∈ m)
    (hq : q' - q ∈ m) (hr : r ∈ m) (h1 : x - p ∉ m) (h2 : x - q ∉ m) :
    t * t - (p' + q') * t + (p' * q' - r * s) ≠ 0 := by
  intro h0
  have e : (x - p) * (x - q) ∈ m := by
    rw [← Ideal.Quotient.eq] at ht hp hq
    rw [← Ideal.Quotient.eq_zero_iff_mem] at hr ⊢
    have := congrArg (Ideal.Quotient.mk m) h0
    simp only [map_add, map_sub, map_mul, map_zero, ht, hp, hq, hr] at this ⊢
    linear_combination this
  rcases hm.mem_or_mem e with e | e
  · exact h1 e
  · exact h2 e

private theorem bd_zero {S : M4 R} (h : IsBlock S) : S 0 1 = 0 ∧ S 0 3 = 0 ∧ S 1 0 = 0 ∧ S 1 2 = 0 ∧ S 2 1 = 0 ∧
    S 2 3 = 0 ∧ S 3 0 = 0 ∧ S 3 2 = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> exact h _ _ (by decide)

end SlopeTestRemainingChoices

theorem UpperTheory.V.Ws.blockDet :
    ∀ {R : Type} [CommRing R] [IsDomain R] [CharZero R] (m : Ideal R) [m.IsPrime] (a : Fin 4 → R) (u v S X : M4 R), v * u = 1 →
          (∀ i j, lamW i ≠ lamW j → a i - a j ∉ m) → IsBlock S → (∀ i j, S i j - Matrix.diagonal a i j ∈ m) → IsUp (v * S * u) →
          (∀ i, (v * S * u) i i - a i ∈ m) → IsBlock X → IsUp (v * X * u) →
          (X.submatrix ixA ixA).det = (v * X * u) 0 0 * (v * X * u) 2 2 ∧ (X.submatrix ixB ixB).det = (v * X * u) 1 1 * (v * X * u) 3 3 := by
  intro R _ _ _ m _ a u v S X hvu ha hS hSa hT hTa hX hY
  have huv : u * v = 1 := mul_eq_one_comm.mp hvu
  obtain ⟨s01, s03, s10, s12, s21, s23, s30, s32⟩ := bd_zero hS
  obtain ⟨x01, x03, x10, x12, x21, x23, x30, x32⟩ := bd_zero hX
  have hd : ∀ i, S i i - a i ∈ m := fun i => by simpa using hSa i i
  have h13 : S 1 3 ∈ m := by simpa using hSa 1 3
  have h02 : S 0 2 ∈ m := by simpa using hSa 0 2
  obtain ⟨N, hN⟩ : ∃ N, N = S * S - (S 1 1 + S 3 3) • S + (S 1 1 * S 3 3 - S 1 3 * S 3 1) • (1 : M4 R) := ⟨_, rfl⟩
  obtain ⟨M, hM⟩ : ∃ N, N = S * S - (S 0 0 + S 2 2) • S + (S 0 0 * S 2 2 - S 0 2 * S 2 0) • (1 : M4 R) := ⟨_, rfl⟩
  have hNz : ∀ i j, (lamW i = 0 ∨ lamW j = 0) → N i j = 0 := by
    intro i j h
    subst hN
    fin_cases i <;> fin_cases j <;> first | (exact absurd h (by decide)) |
      (simp [Matrix.mul_apply, Fin.sum_univ_four, s01, s03, s10, s12, s21, s23, s30, s32]; try ring)
  have hMz : ∀ i j, (lamW i = 1 ∨ lamW j = 1) → M i j = 0 := by
    intro i j h
    subst hM
    fin_cases i <;> fin_cases j <;> first | (exact absurd h (by decide)) |
      (simp [Matrix.mul_apply, Fin.sum_univ_four, s01, s03, s10, s12, s21, s23, s30, s32]; try ring)
  have hNM : N * M = 0 := by
    ext i j
    rw [Matrix.mul_apply, Fin.sum_univ_four, hMz 0 j (Or.inl rfl), hMz 2 j (Or.inl rfl), hNz i 1 (Or.inr rfl),
      hNz i 3 (Or.inr rfl)]
    simp
  have uN : IsUp (v * N * u) := by rw [hN, bd_poly huv hvu]; exact bd_poly_up hT _ _
  have uM : IsUp (v * M * u) := by rw [hM, bd_poly huv hvu]; exact bd_poly_up hT _ _
  have nN : ∀ i, lamW i = 1 → (v * N * u) i i ≠ 0 := by
    intro i hi
    rw [hN, bd_poly huv hvu, bd_poly_diag hT]
    exact bd_notMem m (hTa i) (hd 1) (hd 3) h13 (ha i 1 (by rw [hi]; decide)) (ha i 3 (by rw [hi]; decide))
  have nM : ∀ i, lamW i = 0 → (v * M * u) i i ≠ 0 := by
    intro i hi
    rw [hM, bd_poly huv hvu, bd_poly_diag hT]
    exact bd_notMem m (hTa i) (hd 0) (hd 2) h02 (ha i 0 (by rw [hi]; decide)) (ha i 2 (by rw [hi]; decide))
  have hz : ∀ i, (v * N * u) i i * (v * M * u) i i = 0 := by
    intro i
    rw [← bd_up_diag uN uM, ← bd_conj_mul huv, hNM]; simp
  have n1 : (v * N * u) 1 1 = 0 := (mul_eq_zero.mp (hz 1)).resolve_right (nM 1 rfl)
  have n3 : (v * N * u) 3 3 = 0 := (mul_eq_zero.mp (hz 3)).resolve_right (nM 3 rfl)
  have m0 : (v * M * u) 0 0 = 0 := (mul_eq_zero.mp (hz 0)).resolve_left (nN 0 rfl)
  have m2 : (v * M * u) 2 2 = 0 := (mul_eq_zero.mp (hz 2)).resolve_left (nN 2 rfl)
  have u1 : IsUp (v * 1 * u) := by
    rw [Matrix.mul_one, hvu]; intro i j hij; exact Matrix.one_apply_ne hij.ne'
  have two : (2 : R) ≠ 0 := two_ne_zero
  constructor
  · have k1 := bd_key huv uN u1
    have k2 := bd_key huv uN hY
    have z1 : ∀ i, N i 1 = 0 := fun i => hNz i 1 (Or.inr rfl)
    have z3 : ∀ i, N i 3 = 0 := fun i => hNz i 3 (Or.inr rfl)
    have z1' : ∀ i, N 1 i = 0 := fun i => hNz 1 i (Or.inl rfl)
    have z3' : ∀ i, N 3 i = 0 := fun i => hNz 3 i (Or.inl rfl)
    have p0 := nN 0 rfl
    have p2 := nN 2 rfl
    rw [Matrix.mul_one v, hvu] at k1
    generalize v * N * u = N' at *
    generalize v * X * u = X' at *
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Fin.sum_univ_four, Matrix.mul_one,
      Matrix.one_apply_eq, z1, z3, z1', z3', n1, n3, x01, x03, x10, x12, x21, x23, x30, x32] at k1 k2
    apply mul_left_cancel₀ (mul_ne_zero two (mul_ne_zero p0 p2))
    simp only [Matrix.det_fin_two, Matrix.submatrix_apply, ixA, Matrix.cons_val_zero, Matrix.cons_val_one]
    linear_combination k2 - (X 0 0 * X 2 2 - X 0 2 * X 2 0) * k1
  · have k1 := bd_key huv uM u1
    have k2 := bd_key huv uM hY
    have z1 : ∀ i, M i 0 = 0 := fun i => hMz i 0 (Or.inr rfl)
    have z3 : ∀ i, M i 2 = 0 := fun i => hMz i 2 (Or.inr rfl)
    have z1' : ∀ i, M 0 i = 0 := fun i => hMz 0 i (Or.inl rfl)
    have z3' : ∀ i, M 2 i = 0 := fun i => hMz 2 i (Or.inl rfl)
    have p0 := nM 1 rfl
    have p2 := nM 3 rfl
    rw [Matrix.mul_one v, hvu] at k1
    generalize v * M * u = N' at *
    generalize v * X * u = X' at *
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Fin.sum_univ_four, Matrix.mul_one,
      Matrix.one_apply_eq, z1, z3, z1', z3', m0, m2, x01, x03, x10, x12, x21, x23, x30, x32] at k1 k2
    apply mul_left_cancel₀ (mul_ne_zero two (mul_ne_zero p0 p2))
    simp only [Matrix.det_fin_two, Matrix.submatrix_apply, ixB, Matrix.cons_val_zero, Matrix.cons_val_one]
    linear_combination k2 - (X 1 1 * X 3 3 - X 1 3 * X 3 1) * k1
