import Mathlib

namespace PositivityTheory.Rg.Rsw.L.LGenK

open Matrix

variable {n : Type} [Fintype n] [DecidableEq n]

def cj {R : Type} [CommRing R] (s : R →+* R) {m p : Type} (M : Matrix m p R) : Matrix p m R := (M.map s)ᵀ

theorem cj_apply {R : Type} [CommRing R] (s : R →+* R) {m p : Type} (M : Matrix m p R) (i : p) (j : m) :
    cj s M i j = s (M j i) := rfl

theorem det_prod_transvec {K : Type} [CommRing K] (L : List (TransvectionStruct n K)) :
    (L.map TransvectionStruct.toMatrix).prod.det = 1 := by
  induction L with
  | nil => simp
  | cons t L ih => simp [List.map_cons, List.prod_cons, det_mul, ih, TransvectionStruct.det]

theorem fieldB {K : Type} [Field K] (c d X Y : Matrix n n K) (h : c * X + d * Y = 1) :
    ∃ B : Matrix n n K, (d + c * B).det ≠ 0 := by
  obtain ⟨L, L', D, hD⟩ := Matrix.Pivot.exists_list_transvec_mul_mul_list_transvec_eq_diagonal d
  set P := (L.map TransvectionStruct.toMatrix).prod with hPdef
  set Q := (L'.map TransvectionStruct.toMatrix).prod with hQdef
  have hP : P.det = 1 := det_prod_transvec L
  have hQ : Q.det = 1 := det_prod_transvec L'
  have hPu : IsUnit P.det := by rw [hP]; exact isUnit_one
  have hQu : IsUnit Q.det := by rw [hQ]; exact isUnit_one
  set E' : Matrix n n K := diagonal fun j => 1 - D j * (D j)⁻¹ with hE'
  set N := P * c * X * P⁻¹ with hNdef
  refine ⟨X * P⁻¹ * E' * Q⁻¹, ?_⟩
  have hM : P * (d + c * (X * P⁻¹ * E' * Q⁻¹)) * Q = diagonal D + N * E' := by
    rw [Matrix.mul_add, Matrix.add_mul, hD]
    congr 1
    simp only [hNdef, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hQu, Matrix.mul_one]
  have hPd : P * d = diagonal D * Q⁻¹ := by
    rw [← hD]; simp [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hQu]
  have hN : ∀ i j, D i = 0 → N i j = (1 : Matrix n n K) i j := by
    intro i j hi
    have h1 : N + P * d * Y * P⁻¹ = 1 := by
      calc N + P * d * Y * P⁻¹ = P * (c * X + d * Y) * P⁻¹ := by
              simp [hNdef, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
        _ = 1 := by rw [h, Matrix.mul_one, Matrix.mul_nonsing_inv _ hPu]
    have h2 : (P * d * Y * P⁻¹) i j = 0 := by
      rw [hPd, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.diagonal_mul, hi, zero_mul]
    have := congrFun (congrFun h1 i) j
    rw [Matrix.add_apply, h2, add_zero] at this
    exact this
  intro hdet
  have hM0 : (diagonal D + N * E').det = 0 := by
    rw [← hM, det_mul, det_mul, hdet]; simp
  obtain ⟨p, hp0, hp⟩ := Matrix.exists_vecMul_eq_zero_iff.2 hM0
  apply hp0
  have hME : ∀ i j, (diagonal D + N * E') i j = (if i = j then D i else 0) + N i j * (1 - D j * (D j)⁻¹) := by
    intro i j
    rw [Matrix.add_apply, hE', Matrix.mul_diagonal, Matrix.diagonal_apply]
  have hpj : ∀ j, ∑ i, p i * ((if i = j then D i else 0) + N i j * (1 - D j * (D j)⁻¹)) = 0 := by
    intro j
    have := congrFun hp j
    simp only [Matrix.vecMul, dotProduct, Pi.zero_apply] at this
    refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) this
    rw [hME]
  have h1 : ∀ j, D j ≠ 0 → p j = 0 := by
    intro j hj
    have := hpj j
    simp only [mul_inv_cancel₀ hj, sub_self, mul_zero, add_zero, mul_ite, mul_zero] at this
    rw [Finset.sum_ite_eq' Finset.univ j] at this
    simpa [hj] using this
  funext j
  by_cases hj : D j = 0
  · have := hpj j
    have e : ∀ i, p i * ((if i = j then D i else 0) + N i j * (1 - D j * (D j)⁻¹)) = p i * (1 : Matrix n n K) i j := by
      intro i
      rw [hj, zero_mul, sub_zero, mul_one]
      by_cases hi : D i = 0
      · rw [hN i j hi]
        split_ifs with hij
        · subst hij; simp [hi]
        · simp
      · rw [h1 i hi]; simp
    rw [Finset.sum_congr rfl fun i _ => e i] at this
    simpa [Matrix.one_apply] using this
  · exact h1 j hj

section Cj

variable {R : Type} [CommRing R] (s : R →+* R)

theorem cj_mul {m p q : Type} [Fintype p] (M : Matrix m p R) (N : Matrix p q R) : cj s (M * N) = cj s N * cj s M := by
  ext i j; simp [cj, Matrix.mul_apply, mul_comm]

theorem cj_add {m p : Type} (M N : Matrix m p R) : cj s (M + N) = cj s M + cj s N := by
  ext i j; simp [cj]

theorem cj_sub {m p : Type} (M N : Matrix m p R) : cj s (M - N) = cj s M - cj s N := by
  ext i j; simp [cj]

omit [Fintype n] in
theorem cj_one : cj s (1 : Matrix n n R) = 1 := by
  ext i j; simp [cj, Matrix.one_apply]; split_ifs <;> simp_all [eq_comm]

theorem cj_cj (hs : ∀ x, s (s x) = x) {m p : Type} (M : Matrix m p R) : cj s (cj s M) = M := by
  ext i j; simp [cj, hs]

omit [Fintype n] in
theorem cj_diagonal (f : n → R) : cj s (diagonal f) = diagonal fun i => s (f i) := by
  ext i j; simp [cj, Matrix.diagonal_apply]; split_ifs <;> simp_all [eq_comm]

theorem det_cj (M : Matrix n n R) : (cj s M).det = s M.det := by
  rw [cj, det_transpose, RingHom.map_det]; rfl

end Cj

theorem fieldA {K : Type} [Field K] (s : K →+* K) (hs : ∀ x, s (s x) = x) (c d X Y : Matrix n n K)
    (h : c * X + d * Y = 1) (hl : c * cj s d = d * cj s c) :
    ∃ B : Matrix n n K, cj s B = B ∧ (d + c * B).det ≠ 0 := by
  obtain ⟨L, L', D, hD⟩ := Matrix.Pivot.exists_list_transvec_mul_mul_list_transvec_eq_diagonal c
  set P := (L.map TransvectionStruct.toMatrix).prod with hPdef
  set Q := (L'.map TransvectionStruct.toMatrix).prod with hQdef
  have hP : P.det = 1 := det_prod_transvec L
  have hQ : Q.det = 1 := det_prod_transvec L'
  have hPu : IsUnit P.det := by rw [hP]; exact isUnit_one
  have hQu : IsUnit Q.det := by rw [hQ]; exact isUnit_one
  have hQQ : Q * Q⁻¹ = 1 := Matrix.mul_nonsing_inv _ hQu
  have hQQ' : Q⁻¹ * Q = 1 := Matrix.nonsing_inv_mul _ hQu
  set R' := cj s Q⁻¹ with hR'
  have hR1 : cj s Q * R' = 1 := by rw [hR', ← cj_mul, hQQ', cj_one]
  have hR2 : R' * cj s Q = 1 := by rw [hR', ← cj_mul, hQQ, cj_one]
  set d' := P * d * R' with hd'
  set H := diagonal D * cj s d' with hH
  have hH' : H = P * (c * cj s d) * cj s P := by
    rw [hH, hd', ← hD, cj_mul, cj_mul, hR', cj_cj s hs]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Q, hQQ, Matrix.one_mul]
  have hHh : cj s H = H := by
    rw [hH', cj_mul, cj_mul, cj_mul, cj_cj s hs, cj_cj s hs, ← hl]
    simp only [Matrix.mul_assoc]
  have hHij : ∀ i j, H i j = D i * s (d' j i) := by
    intro i j; rw [hH, Matrix.diagonal_mul]; rfl
  have hHsym : ∀ i j, H i j = s (D j) * d' i j := by
    intro i j
    have := congrFun (congrFun hHh i) j
    rw [cj_apply, hHij j i, map_mul, hs] at this
    exact this.symm
  set e : n → K := fun i => D i * (D i)⁻¹ with he
  have hse : ∀ i, s (e i) = e i := by
    intro i; by_cases h0 : D i = 0
    · simp [he, h0]
    · simp [he, h0, mul_inv_cancel₀]
  set E : Matrix n n K := diagonal e with hE
  set Dp : Matrix n n K := diagonal fun i => (D i)⁻¹ with hDp
  obtain ⟨b', hb'⟩ : ∃ b', b' = Dp * (E - E * H * E) * cj s Dp := ⟨_, rfl⟩
  have hcE : cj s E = E := by rw [hE, cj_diagonal]; congr 1; funext i; exact hse i
  have hb'h : cj s b' = b' := by
    rw [hb', cj_mul, cj_mul, cj_sub, cj_mul, cj_mul, cj_cj s hs, hcE, hHh]
    simp only [Matrix.mul_assoc]
  refine ⟨Q * b' * cj s Q, ?_, ?_⟩
  · rw [cj_mul, cj_mul, cj_cj s hs, hb'h, Matrix.mul_assoc]
  have hM : P * (d + c * (Q * b' * cj s Q)) * R' = d' + diagonal D * b' := by
    rw [Matrix.mul_add, Matrix.add_mul, hd', ← hD]
    congr 1
    simp only [Matrix.mul_assoc, hR1, Matrix.mul_one]

  have hcol : ∀ i j, D j ≠ 0 → (d' + diagonal D * b') i j = if i = j then (s (D j))⁻¹ else 0 := by
    intro i j hj
    have hsj : s (D j) ≠ 0 := fun h0 => hj (by rw [← hs (D j), h0, map_zero])
    have hb'ij : b' i j = (D i)⁻¹ * ((if i = j then e i else 0) - e i * H i j * e j) * s ((D j)⁻¹) := by
      rw [hb', cj_diagonal, Matrix.mul_diagonal, hDp, Matrix.diagonal_mul, Matrix.sub_apply, hE,
        Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.diagonal_apply]
    rw [Matrix.add_apply, Matrix.diagonal_mul, hb'ij, map_inv₀]
    have hej : e j = 1 := by simp [he, hj]
    rw [hej, mul_one]
    by_cases hi : D i = 0
    · have hd0 : d' i j = 0 := by
        have := hHsym i j
        rw [hHij, hi, zero_mul] at this
        exact (mul_eq_zero.1 this.symm).resolve_left hsj
      have hij : i ≠ j := fun h => hj (h ▸ hi)
      simp [hi, hd0, hij]
    · have hei : e i = 1 := by simp [he, hi]
      rw [hei, hHsym]
      split_ifs with hij
      · subst hij; field_simp; ring
      · field_simp; ring
  intro hdet
  have hM0 : (d' + diagonal D * b').det = 0 := by
    rw [← hM, det_mul, det_mul, hdet]; simp
  obtain ⟨p, hp0, hp⟩ := Matrix.exists_vecMul_eq_zero_iff.2 hM0
  apply hp0
  have h1 : ∀ j, D j ≠ 0 → p j = 0 := by
    intro j hj
    have := congrFun hp j
    simp only [Matrix.vecMul, dotProduct, Pi.zero_apply] at this
    rw [Finset.sum_congr rfl fun i _ => by rw [hcol i j hj]] at this
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at this
    have hsj : s (D j) ≠ 0 := fun h0 => hj (by rw [← hs (D j), h0, map_zero])
    exact (mul_eq_zero.1 this).resolve_right (inv_ne_zero hsj)
  have hpD : p ᵥ* diagonal D = 0 := by
    funext j; rw [Matrix.vecMul_diagonal]
    by_cases hj : D j = 0
    · simp [hj]
    · simp [h1 j hj]
  have hpd' : p ᵥ* d' = 0 := by
    have := hp
    rw [Matrix.vecMul_add, ← Matrix.vecMul_vecMul p (diagonal D) b', hpD, Matrix.zero_vecMul, add_zero] at this
    exact this
  set q := p ᵥ* P with hq
  have hqc : q ᵥ* c = 0 := by
    have e1 : q ᵥ* c ᵥ* Q = 0 := by
      rw [hq, Matrix.vecMul_vecMul, Matrix.vecMul_vecMul, ← Matrix.mul_assoc, hD]; exact hpD
    calc q ᵥ* c = q ᵥ* c ᵥ* (Q * Q⁻¹) := by rw [hQQ, Matrix.vecMul_one]
      _ = 0 := by rw [← Matrix.vecMul_vecMul, e1, Matrix.zero_vecMul]
  have hqd : q ᵥ* d = 0 := by
    have e1 : q ᵥ* d ᵥ* R' = 0 := by
      rw [hq, Matrix.vecMul_vecMul, Matrix.vecMul_vecMul, ← Matrix.mul_assoc]; exact hpd'
    calc q ᵥ* d = q ᵥ* d ᵥ* (R' * cj s Q) := by rw [hR2, Matrix.vecMul_one]
      _ = 0 := by rw [← Matrix.vecMul_vecMul, e1, Matrix.zero_vecMul]
  have hq0 : q = 0 := by
    calc q = q ᵥ* (c * X + d * Y) := by rw [h, Matrix.vecMul_one]
      _ = 0 := by rw [Matrix.vecMul_add, ← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul, hqc, hqd]; simp
  calc p = p ᵥ* (P * P⁻¹) := by rw [Matrix.mul_nonsing_inv _ hPu, Matrix.vecMul_one]
    _ = 0 := by rw [← Matrix.vecMul_vecMul, ← hq, hq0, Matrix.zero_vecMul]

end PositivityTheory.Rg.Rsw.L.LGenK
