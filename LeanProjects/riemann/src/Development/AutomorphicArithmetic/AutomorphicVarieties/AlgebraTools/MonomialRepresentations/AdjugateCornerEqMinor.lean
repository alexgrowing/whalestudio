import Mathlib

open Polynomial Matrix

private def m2 {R : Type} [CommRing R] (A : Matrix (Fin 4) (Fin 4) R) (i j : Fin 4) : R :=
  A i i * A j j - A i j * A j i

private def m3 {R : Type} [CommRing R] (A : Matrix (Fin 4) (Fin 4) R) (i j k : Fin 4) : R :=
  A i i * A j j * A k k - A i i * A j k * A k j - A i j * A j i * A k k + A i j * A j k * A k i
    + A i k * A j i * A k j - A i k * A j j * A k i

private def dsc {R : Type} [CommRing R] (b c d e : R) : R :=
  256 * e ^ 3 - 192 * b * d * e ^ 2 - 128 * c ^ 2 * e ^ 2 + 144 * c * d ^ 2 * e - 27 * d ^ 4
   + 144 * b ^ 2 * c * e ^ 2 - 6 * b ^ 2 * d ^ 2 * e - 80 * b * c ^ 2 * d * e + 18 * b * c * d ^ 3
   + 16 * c ^ 4 * e - 4 * c ^ 3 * d ^ 2 - 27 * b ^ 4 * e ^ 2 + 18 * b ^ 3 * c * d * e
   - 4 * b ^ 3 * d ^ 3 - 4 * b ^ 2 * c ^ 3 * e + b ^ 2 * c ^ 2 * d ^ 2

private def tm {R : Type} [CommRing R] (b c d e : R) (k : ℤ) (i j l m : ℕ) : R :=
  (k : R) * b ^ i * c ^ j * d ^ l * e ^ m

private theorem valuation_tm_le_exp {F : Type} [Field F] (v : Valuation F (WithZero (Multiplicative ℤ)))
    (hk : ∀ k : ℤ, v (k : F) ≤ 1) {b c d e : F} {β γ δ ε : ℤ}
    (hb : v b ≤ WithZero.exp β) (hc : v c ≤ WithZero.exp γ) (hd : v d ≤ WithZero.exp δ)
    (he : v e ≤ WithZero.exp ε) (k : ℤ) (i j l m : ℕ) :
    v (tm b c d e k i j l m) ≤ WithZero.exp (i * β + j * γ + l * δ + m * ε) := by
  have h1 : WithZero.exp ((i:ℤ) * β + j * γ + l * δ + m * ε)
      = 1 * WithZero.exp β ^ i * WithZero.exp γ ^ j * WithZero.exp δ ^ l * WithZero.exp ε ^ m := by
    simp only [WithZero.exp_add, ← WithZero.exp_nsmul, one_mul, nsmul_eq_mul]
  rw [h1, tm, map_mul, map_mul, map_mul, map_mul, map_pow, map_pow, map_pow, map_pow]
  gcongr
  exact hk k

private theorem dsc_ne_zero_of_valuation_strict_chain {F : Type} [Field F] (v : Valuation F (WithZero (Multiplicative ℤ)))
    (hk : ∀ k : ℤ, v (k : F) ≤ 1) {b c d e : F} {w0 w1 w2 w3 : ℤ}
    (h01 : w1 < w0) (h12 : w2 < w1) (h23 : w3 < w2)
    (hb : v b = WithZero.exp w0) (hc : v c = WithZero.exp (w0 + w1))
    (hd : v d = WithZero.exp (w0 + w1 + w2)) (he : v e ≤ WithZero.exp (w0 + w1 + w2 + w3)) :
    dsc b c d e ≠ 0 := by
  intro h0
  have key : dsc b c d e = b ^ 2 * c ^ 2 * d ^ 2 + (tm b c d e 256 0 0 0 3 + tm b c d e (-192) 1 0 1 2
      + tm b c d e (-128) 0 2 0 2 + tm b c d e 144 0 1 2 1 + tm b c d e (-27) 0 0 4 0
      + tm b c d e 144 2 1 0 2 + tm b c d e (-6) 2 0 2 1 + tm b c d e (-80) 1 2 1 1
      + tm b c d e 18 1 1 3 0 + tm b c d e 16 0 4 0 1 + tm b c d e (-4) 0 3 2 0
      + tm b c d e (-27) 4 0 0 2 + tm b c d e 18 3 1 1 1 + tm b c d e (-4) 3 0 3 0
      + tm b c d e (-4) 2 3 0 1) := by
    simp only [dsc, tm]
    push_cast
    ring
  have hL : v (b ^ 2 * c ^ 2 * d ^ 2) = WithZero.exp (2 * w0 + 2 * (w0 + w1) + 2 * (w0 + w1 + w2)) := by
    rw [map_mul, map_mul, map_pow, map_pow, map_pow, hb, hc, hd]
    simp only [← WithZero.exp_nsmul, ← WithZero.exp_add, nsmul_eq_mul]
    congr 1 <;> ring
  rw [key] at h0
  have hR : v (tm b c d e 256 0 0 0 3 + tm b c d e (-192) 1 0 1 2
      + tm b c d e (-128) 0 2 0 2 + tm b c d e 144 0 1 2 1 + tm b c d e (-27) 0 0 4 0
      + tm b c d e 144 2 1 0 2 + tm b c d e (-6) 2 0 2 1 + tm b c d e (-80) 1 2 1 1
      + tm b c d e 18 1 1 3 0 + tm b c d e 16 0 4 0 1 + tm b c d e (-4) 0 3 2 0
      + tm b c d e (-27) 4 0 0 2 + tm b c d e 18 3 1 1 1 + tm b c d e (-4) 3 0 3 0
      + tm b c d e (-4) 2 3 0 1) < v (b ^ 2 * c ^ 2 * d ^ 2) := by
    rw [hL]
    repeat' apply Valuation.map_add_lt
    all_goals
      exact lt_of_le_of_lt (valuation_tm_le_exp v hk hb.le hc.le hd.le he _ _ _ _ _)
        (WithZero.exp_lt_exp.2 (by push_cast; linarith))
  have := Valuation.map_add_eq_of_lt_left v hR
  rw [h0, map_zero, hL] at this
  exact WithZero.exp_ne_zero this.symm

private theorem dsc_ne_zero_of_valuation_c_le {F : Type} [Field F] (v : Valuation F (WithZero (Multiplicative ℤ)))
    (hk : ∀ k : ℤ, v (k : F) ≤ 1) (h4 : v (4 : F) = 1) {b c d e : F} {w0 w1 w2 w3 : ℤ}
    (h01 : w1 < w0) (h12 : w2 < w1) (h23 : w3 < w2)
    (hb : v b = WithZero.exp w0) (hc : v c ≤ WithZero.exp (w0 + w2))
    (hd : v d = WithZero.exp (w0 + w1 + w2)) (he : v e ≤ WithZero.exp (w0 + w1 + w2 + w3)) :
    dsc b c d e ≠ 0 := by
  intro h0
  have key : dsc b c d e = -(4 * (b ^ 3 * d ^ 3)) + (tm b c d e 256 0 0 0 3 + tm b c d e (-192) 1 0 1 2
      + tm b c d e (-128) 0 2 0 2 + tm b c d e 144 0 1 2 1 + tm b c d e (-27) 0 0 4 0
      + tm b c d e 144 2 1 0 2 + tm b c d e (-6) 2 0 2 1 + tm b c d e (-80) 1 2 1 1
      + tm b c d e 18 1 1 3 0 + tm b c d e 16 0 4 0 1 + tm b c d e (-4) 0 3 2 0
      + tm b c d e (-27) 4 0 0 2 + tm b c d e 18 3 1 1 1 + tm b c d e 1 2 2 2 0
      + tm b c d e (-4) 2 3 0 1) := by
    simp only [dsc, tm]
    push_cast
    ring
  have hL : v (-(4 * (b ^ 3 * d ^ 3))) = WithZero.exp (3 * w0 + 3 * (w0 + w1 + w2)) := by
    rw [Valuation.map_neg, map_mul, map_mul, map_pow, map_pow, h4, hb, hd, one_mul]
    simp only [← WithZero.exp_nsmul, ← WithZero.exp_add, nsmul_eq_mul]
    congr 1 <;> ring
  rw [key] at h0
  have hR : v (tm b c d e 256 0 0 0 3 + tm b c d e (-192) 1 0 1 2
      + tm b c d e (-128) 0 2 0 2 + tm b c d e 144 0 1 2 1 + tm b c d e (-27) 0 0 4 0
      + tm b c d e 144 2 1 0 2 + tm b c d e (-6) 2 0 2 1 + tm b c d e (-80) 1 2 1 1
      + tm b c d e 18 1 1 3 0 + tm b c d e 16 0 4 0 1 + tm b c d e (-4) 0 3 2 0
      + tm b c d e (-27) 4 0 0 2 + tm b c d e 18 3 1 1 1 + tm b c d e 1 2 2 2 0
      + tm b c d e (-4) 2 3 0 1) < v (-(4 * (b ^ 3 * d ^ 3))) := by
    rw [hL]
    repeat' apply Valuation.map_add_lt
    all_goals
      exact lt_of_le_of_lt (valuation_tm_le_exp v hk hb.le hc hd.le he _ _ _ _ _)
        (WithZero.exp_lt_exp.2 (by push_cast; linarith))
  have := Valuation.map_add_eq_of_lt_left v hR
  rw [h0, map_zero, hL] at this
  exact WithZero.exp_ne_zero this.symm

private theorem separable_quartic_of_dsc_ne_zero {F : Type} [Field F] (b c d e : F) (h : dsc b c d e ≠ 0) :
    (X ^ 4 + C b * X ^ 3 + C c * X ^ 2 + C d * X + C e : F[X]).Separable := by
  classical
  by_contra hns
  set f : F[X] := X ^ 4 + C b * X ^ 3 + C c * X ^ 2 + C d * X + C e with hf
  have hdeg : f.natDegree = 4 := by
    rw [hf]
    compute_degree!
  have hf0 : f ≠ 0 := by
    intro h0
    rw [h0] at hdeg
    simp at hdeg
  have hsplit : (f.map (algebraMap F (AlgebraicClosure F))).Splits := IsAlgClosed.splits _
  have hnd : ¬ (f.map (algebraMap F (AlgebraicClosure F))).roots.Nodup := by
    rw [nodup_roots_iff_of_splits (Polynomial.map_ne_zero hf0) hsplit, separable_map]
    exact hns
  rw [Multiset.nodup_iff_count_le_one] at hnd
  push_neg at hnd
  obtain ⟨r, hr⟩ := hnd
  rw [count_roots] at hr
  obtain ⟨h0, h1⟩ := (one_lt_rootMultiplicity_iff_isRoot (Polynomial.map_ne_zero hf0)).1 hr
  apply h
  apply (algebraMap F (AlgebraicClosure F)).injective
  rw [map_zero]
  have hm : algebraMap F (AlgebraicClosure F) (dsc b c d e) = dsc (algebraMap F (AlgebraicClosure F) b)
      (algebraMap F (AlgebraicClosure F) c) (algebraMap F (AlgebraicClosure F) d)
      (algebraMap F (AlgebraicClosure F) e) := by
    simp only [dsc, map_sub, map_add, map_mul, map_pow, map_ofNat]
  rw [hm]
  simp [hf, IsRoot] at h0 h1
  have hd : algebraMap F (AlgebraicClosure F) d = -(4 * r ^ 3 + 3 * (algebraMap F (AlgebraicClosure F) b) * r ^ 2
      + 2 * (algebraMap F (AlgebraicClosure F) c) * r) := by
    linear_combination h1
  have he : algebraMap F (AlgebraicClosure F) e = -(r ^ 4 + (algebraMap F (AlgebraicClosure F) b) * r ^ 3
      + (algebraMap F (AlgebraicClosure F) c) * r ^ 2 + (algebraMap F (AlgebraicClosure F) d) * r) := by
    linear_combination h0
  rw [he, hd]
  unfold dsc
  ring

private theorem charpoly_fin_four_eq {R : Type} [CommRing R] (A : Matrix (Fin 4) (Fin 4) R) :
    A.charpoly = X ^ 4 + C (-(A 0 0 + A 1 1 + A 2 2 + A 3 3)) * X ^ 3
      + C (m2 A 0 1 + m2 A 0 2 + m2 A 0 3 + m2 A 1 2 + m2 A 1 3 + m2 A 2 3) * X ^ 2
      + C (-(m3 A 0 1 2 + m3 A 0 1 3 + m3 A 0 2 3 + m3 A 1 2 3)) * X + C A.det := by
  simp only [Matrix.charpoly, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Matrix.det_fin_zero, charmatrix_apply, Matrix.submatrix_apply, m2, m3]
  simp [Fin.succAbove, Fin.lt_def, Matrix.one_apply, Matrix.diagonal_apply, Fin.ext_iff]
  ring

private theorem valuation_add_eq_of_valuation_lt {F : Type} [Field F] (v : Valuation F (WithZero (Multiplicative ℤ)))
    {a r : F} {n : ℤ} (ha : v a = WithZero.exp n) (hr : v r < WithZero.exp n) :
    v (a + r) = WithZero.exp n := by
  rw [Valuation.map_add_eq_of_lt_left v (ha ▸ hr), ha]

open WithZero in
theorem UpperTheory.V.AlgebraTools.disc4 :
    ∀ (K : Type) [Field K], (2 : K) ≠ 0 → ∀ (x : Matrix (Fin 4) (Fin 4) K) (w : Fin 4 → ℤ), StrictAnti w → x 0 0 ≠ 0 → x.adjugate 3 3 ≠ 0 →
      (x.map (algebraMap K (RatFunc K)) * diagonal (fun i => (RatFunc.X : RatFunc K) ^ w i)).charpoly.Separable := by
  intro K _ h2 x w hw hx0 hadj
  classical
  set v := RatFunc.inftyValuation K with hv
  set φ := algebraMap K (RatFunc K) with hφdef
  have hφ1 : ∀ a : K, a ≠ 0 → v (φ a) = 1 := fun a ha => Valuation.IsTrivialOn.eq_one a ha
  have hφ : ∀ a : K, v (φ a) ≤ 1 := by
    intro a
    by_cases ha : a = 0
    · simp [ha]
    · rw [hφ1 a ha]
  have ht : ∀ n : ℤ, v ((RatFunc.X : RatFunc K) ^ n) = WithZero.exp n :=
    fun n => RatFunc.inftyValuation.X_zpow K n
  have hk : ∀ k : ℤ, v (k : RatFunc K) ≤ 1 := by
    intro k
    rw [← map_intCast φ k]
    exact hφ _
  have h4 : v (4 : RatFunc K) = 1 := by
    rw [← map_ofNat φ 4]
    apply hφ1
    intro h
    apply h2
    have h22 : (4 : K) = 2 * 2 := by norm_num
    rw [h22] at h
    exact mul_self_eq_zero.1 h
  have hT : ∀ (a : K) (n : ℤ), v (φ a * RatFunc.X ^ n) ≤ WithZero.exp n := by
    intro a n
    rw [map_mul, ht]
    calc v (φ a) * WithZero.exp n ≤ 1 * WithZero.exp n := by
          gcongr
          exact hφ a
      _ = WithZero.exp n := one_mul _
  have hT1 : ∀ (a : K) (n : ℤ), a ≠ 0 → v (φ a * RatFunc.X ^ n) = WithZero.exp n := by
    intro a n ha
    rw [map_mul, ht, hφ1 a ha, one_mul]
  have h01 : w 1 < w 0 := hw (by decide)
  have h12 : w 2 < w 1 := hw (by decide)
  have h23 : w 3 < w 2 := hw (by decide)
  have hX0 : (RatFunc.X : RatFunc K) ≠ 0 := RatFunc.X_ne_zero
  set A := x.map φ * diagonal (fun i => (RatFunc.X : RatFunc K) ^ w i) with hAdef
  have hA : ∀ i j, A i j = φ (x i j) * RatFunc.X ^ w j := by
    intro i j
    simp [hAdef, Matrix.mul_diagonal]
  have hm2 : ∀ i j, m2 A i j = φ (m2 x i j) * RatFunc.X ^ (w i + w j) := by
    intro i j
    simp only [m2, hA, map_sub, map_mul, zpow_add₀ hX0]
    ring
  have hm3 : ∀ i j k, m3 A i j k = φ (m3 x i j k) * RatFunc.X ^ (w i + w j + w k) := by
    intro i j k
    simp only [m3, hA, map_sub, map_add, map_mul, zpow_add₀ hX0]
    ring
  have hdm : (x.map φ).det = φ x.det := by
    rw [RingHom.map_det]
    rfl
  have hdet : A.det = φ x.det * RatFunc.X ^ (w 0 + w 1 + w 2 + w 3) := by
    rw [hAdef, Matrix.det_mul, hdm, Matrix.det_diagonal, Fin.prod_univ_four]
    simp only [zpow_add₀ hX0]
    all_goals ring
  have hadj' : m3 x 0 1 2 ≠ 0 := by
    have hh : x.adjugate 3 3 = m3 x 0 1 2 := by
      rw [Matrix.adjugate_fin_succ_eq_det_submatrix, Matrix.det_fin_three]
      simp [m3, Fin.succAbove, Fin.lt_def]
      ring
    rwa [hh] at hadj
  rw [charpoly_fin_four_eq A]
  apply separable_quartic_of_dsc_ne_zero
  have hb : v (-(A 0 0 + A 1 1 + A 2 2 + A 3 3)) = WithZero.exp (w 0) := by
    rw [Valuation.map_neg, hA, hA, hA, hA, add_assoc, add_assoc]
    apply valuation_add_eq_of_valuation_lt v (hT1 _ _ hx0)
    repeat' apply Valuation.map_add_lt
    all_goals exact lt_of_le_of_lt (hT _ _) (WithZero.exp_lt_exp.2 (by linarith))
  have hd : v (-(m3 A 0 1 2 + m3 A 0 1 3 + m3 A 0 2 3 + m3 A 1 2 3)) = WithZero.exp (w 0 + w 1 + w 2) := by
    rw [Valuation.map_neg, hm3, hm3, hm3, hm3, add_assoc, add_assoc]
    apply valuation_add_eq_of_valuation_lt v (hT1 _ _ hadj')
    repeat' apply Valuation.map_add_lt
    all_goals exact lt_of_le_of_lt (hT _ _) (WithZero.exp_lt_exp.2 (by linarith))
  have he : v A.det ≤ WithZero.exp (w 0 + w 1 + w 2 + w 3) := by
    rw [hdet]
    exact hT _ _
  by_cases hz : m2 x 0 1 = 0
  · have hc : v (m2 A 0 1 + m2 A 0 2 + m2 A 0 3 + m2 A 1 2 + m2 A 1 3 + m2 A 2 3)
        ≤ WithZero.exp (w 0 + w 2) := by
      rw [hm2, hm2, hm2, hm2, hm2, hm2, hz, map_zero, zero_mul, zero_add]
      repeat' apply Valuation.map_add_le
      all_goals exact le_trans (hT _ _) (WithZero.exp_le_exp.2 (by linarith))
    exact dsc_ne_zero_of_valuation_c_le v hk h4 h01 h12 h23 hb hc hd he
  · have hc : v (m2 A 0 1 + m2 A 0 2 + m2 A 0 3 + m2 A 1 2 + m2 A 1 3 + m2 A 2 3)
        = WithZero.exp (w 0 + w 1) := by
      rw [hm2, hm2, hm2, hm2, hm2, hm2, add_assoc, add_assoc, add_assoc, add_assoc]
      apply valuation_add_eq_of_valuation_lt v (hT1 _ _ hz)
      repeat' apply Valuation.map_add_lt
      all_goals exact lt_of_le_of_lt (hT _ _) (WithZero.exp_lt_exp.2 (by linarith))
    exact dsc_ne_zero_of_valuation_strict_chain v hk h01 h12 h23 hb hc hd he
