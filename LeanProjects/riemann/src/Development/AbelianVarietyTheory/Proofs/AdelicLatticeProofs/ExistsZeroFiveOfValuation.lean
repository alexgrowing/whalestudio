import Mathlib

open NumberField IsDedekindDomain
open scoped Matrix WithZero

namespace GlobalTheory.LocalQuad

namespace FiveVar

variable {K : Type*} [Field K] {n : Type*} [Fintype n]

def qf (a x : n → K) : K := ∑ i, a i * x i ^ 2

def bf (a x y : n → K) : K := ∑ i, 2 * a i * x i * y i

lemma qf_add (a x y : n → K) : qf a (x + y) = qf a x + bf a x y + qf a y := by
  simp only [qf, bf, ← Finset.sum_add_distrib, Pi.add_apply]
  exact Finset.sum_congr rfl fun i _ => by ring

lemma qf_smul (a x : n → K) (s : K) : qf a (s • x) = s ^ 2 * qf a x := by
  simp only [qf, Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun i _ => by ring

lemma bf_smul_left (a x y : n → K) (s : K) : bf a (s • x) y = s * bf a x y := by
  simp only [bf, Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun i _ => by ring

lemma bf_smul_right (a x y : n → K) (s : K) : bf a x (s • y) = s * bf a x y := by
  simp only [bf, Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun i _ => by ring

lemma bf_add_left (a x y z : n → K) : bf a (x + y) z = bf a x z + bf a y z := by
  simp only [bf, ← Finset.sum_add_distrib, Pi.add_apply]
  exact Finset.sum_congr rfl fun i _ => by ring

lemma bf_self (a x : n → K) : bf a x x = 2 * qf a x := by
  simp only [bf, qf, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

lemma qf_three (a p q r : n → K) (x : Fin 3 → K) (w : K) :
    qf a (x 0 • p + x 1 • q + x 2 • r) / w = ∑ i, ∑ j,
      (![![qf a p / w, bf a p q / w, bf a p r / w], ![0, qf a q / w, bf a q r / w],
        ![0, 0, qf a r / w]] : Fin 3 → Fin 3 → K) i j * x i * x j := by
  rw [qf_add, qf_add, bf_add_left]
  simp [Fin.sum_univ_three, qf_smul, bf_smul_left, bf_smul_right]
  ring

lemma val_bf_sq_le (h2 : (2 : K) ≠ 0) (v : Valuation K ℤᵐ⁰)
    (hsq : ∀ x : K, v (x - 1) < v 4 → IsSquare x) (a : n → K)
    (han : ∀ x, qf a x = 0 → x = 0) (x y : n → K) :
    v (bf a x y) ^ 2 ≤ v (qf a x) * v (qf a y) := by
  by_contra hlt
  rw [not_le] at hlt
  have hb : bf a x y ≠ 0 := by
    intro h
    rw [h] at hlt
    simp at hlt
  have hvb : v (bf a x y) ≠ 0 := by simpa using hb
  have h4 : (4 : K) ≠ 0 := by
    have : (4 : K) = 2 * 2 := by norm_num
    rw [this]; exact mul_ne_zero h2 h2
  have hv4 : v 4 ≠ 0 := by simpa using h4
  have hv4' : v 4 ≤ 1 := by
    have e : (4 : K) = 1 + 1 + 1 + 1 := by norm_num
    have h1 : v 1 ≤ 1 := (map_one v).le
    rw [e]
    exact v.map_add_le (v.map_add_le (v.map_add_le h1 h1) h1) h1
  have hx : qf a x ≠ 0 := by
    intro h
    apply hb
    rw [han x h]
    simp [bf]
  obtain ⟨s, hs⟩ := hsq (1 - 4 * (qf a x * qf a y) / bf a x y ^ 2) (by
    rw [sub_sub_cancel_left, Valuation.map_neg, map_div₀, map_mul, map_mul, map_pow,
      mul_div_assoc]
    have h1 : v (qf a x) * v (qf a y) / v (bf a x y) ^ 2 < 1 :=
      (div_lt_one₀ (pow_pos (zero_lt_iff.mpr hvb) 2)).mpr hlt
    calc v 4 * (v (qf a x) * v (qf a y) / v (bf a x y) ^ 2) < v 4 * 1 :=
          mul_lt_mul_of_pos_left h1 (zero_lt_iff.mpr hv4)
      _ = v 4 := mul_one _)
  set t := (-bf a x y + bf a x y * s) / (2 * qf a x) with ht
  have h0 : qf a (t • x + y) = 0 := by
    rw [qf_add, qf_smul, bf_smul_left, ht]
    have hs' : 4 * (qf a x * qf a y) = bf a x y ^ 2 * (1 - s * s) := by
      rw [← hs]; field_simp; ring
    have : qf a y = bf a x y ^ 2 * (1 - s * s) / (4 * qf a x) := by
      rw [← hs']; field_simp
    rw [this]
    have h4' : (4 : K) = 2 * 2 := by norm_num
    rw [h4']
    field_simp
    ring
  have hy : y = (-t) • x := by
    have := han _ h0
    rw [neg_smul]
    exact eq_neg_of_add_eq_zero_right this
  clear_value t
  subst hy
  rw [bf_smul_right, bf_self, qf_smul] at hlt
  have e : ((-t) * (2 * qf a x)) ^ 2 = 4 * (qf a x * ((-t) ^ 2 * qf a x)) := by ring
  rw [← map_pow, e, ← map_mul v (qf a x), map_mul v 4] at hlt
  exact absurd hlt (not_lt.mpr (mul_le_of_le_one_left' hv4'))

variable [DecidableEq n]

lemma val_det_le (h2 : (2 : K) ≠ 0) (v : Valuation K ℤᵐ⁰)
    (hsq : ∀ x : K, v (x - 1) < v 4 → IsSquare x) (a : n → K)
    (han : ∀ x, qf a x = 0 → x = 0) (P : Matrix n n K) :
    v (∏ i, 2 * a i) * v P.det ^ 2 ≤ ∏ i, v (qf a (P i)) := by
  have hB : P * Matrix.diagonal (fun i => 2 * a i) * Pᵀ =
      Matrix.of fun i j => bf a (P i) (P j) := by
    ext i j
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Matrix.of_apply, bf]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hd := congrArg Matrix.det hB
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal] at hd
  have e : v (∏ i, 2 * a i) * v P.det ^ 2 = v (P.det * (∏ i, 2 * a i) * P.det) := by
    rw [map_mul, map_mul, sq, mul_comm (v P.det) (v (∏ i, 2 * a i)), mul_assoc]
  rw [e, hd, Matrix.det_apply']
  apply Valuation.map_sum_le
  intro σ _
  have hε : v (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : K) = 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
  rw [map_mul, hε, one_mul, map_prod]
  apply le_of_pow_le_pow_left₀ (n := 2) two_ne_zero zero_le'
  rw [← Finset.prod_pow]
  calc ∏ i, v (Matrix.of (fun i j => bf a (P i) (P j)) (σ i) i) ^ 2
      ≤ ∏ i, (v (qf a (P (σ i))) * v (qf a (P i))) :=
        Finset.prod_le_prod' fun i _ => val_bf_sq_le h2 v hsq a han _ _
    _ = (∏ i, v (qf a (P i))) ^ 2 := by
        rw [Finset.prod_mul_distrib, Equiv.prod_comp σ (fun i => v (qf a (P i))), sq]

lemma exists_basis (h2 : (2 : K) ≠ 0) (v : Valuation K ℤᵐ⁰)
    (hsq : ∀ x : K, v (x - 1) < v 4 → IsSquare x) (a : n → K)
    (han : ∀ x, qf a x = 0 → x = 0) :
    ∃ P : Matrix n n K, (∀ j, qf a (P j) ≠ 0) ∧
      ∀ (c : n → K) (j : n), v (c j) ^ 2 * v (qf a (P j)) ≤ v (qf a (∑ k, c k • P k)) := by
  have hrow : ∀ P : Matrix n n K, P.det ≠ 0 → ∀ j, qf a (P j) ≠ 0 := by
    intro P hP j h
    exact hP (Matrix.det_eq_zero_of_row_eq_zero j fun k => congrFun (han _ h) k)
  have ha : ∀ i, a i ≠ 0 := by
    intro i h
    have := hrow 1 (by simp) i
    apply this
    unfold qf
    apply Finset.sum_eq_zero
    intro k _
    by_cases hk : i = k
    · subst hk; simp [h]
    · simp [Matrix.one_apply_ne hk]
  have hD : v (∏ i, 2 * a i) ≠ 0 := by
    rw [Valuation.ne_zero_iff]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => mul_ne_zero h2 (ha i)
  have hprod : ∀ P : Matrix n n K, P.det ≠ 0 → (∏ i, v (qf a (P i))) / v P.det ^ 2 ≠ 0 := by
    intro P hP
    refine div_ne_zero (Finset.prod_ne_zero_iff.mpr fun i _ => ?_) (pow_ne_zero _ ?_)
    · rw [Valuation.ne_zero_iff]; exact hrow P hP i
    · rw [Valuation.ne_zero_iff]; exact hP
  obtain ⟨m, ⟨P, hP, hm⟩, hmin⟩ := Int.exists_least_of_bdd
    (P := fun z => ∃ P : Matrix n n K, P.det ≠ 0 ∧
      WithZero.log ((∏ i, v (qf a (P i))) / v P.det ^ 2) = z)
    ⟨WithZero.log (v (∏ i, 2 * a i)), by
      rintro z ⟨P, hP, rfl⟩
      rw [WithZero.log_le_log hD (hprod P hP), le_div_iff₀
        (pow_pos (zero_lt_iff.mpr ((Valuation.ne_zero_iff v).mpr hP)) 2)]
      exact val_det_le h2 v hsq a han P⟩
    ⟨_, 1, by simp, rfl⟩
  refine ⟨P, hrow P hP, fun c j => ?_⟩
  by_cases hc : c j = 0
  · simp [hc]
  have hdet : (P.updateRow j (∑ k, c k • P k)).det = c j * P.det := by
    rw [Matrix.det_updateRow_sum, smul_eq_mul]
  have hP' : (P.updateRow j (∑ k, c k • P k)).det ≠ 0 := by
    rw [hdet]; exact mul_ne_zero hc hP
  have h := hmin _ ⟨_, hP', rfl⟩
  rw [← hm, WithZero.log_le_log (hprod P hP) (hprod _ hP'), hdet,
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ j),
    ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j), Matrix.updateRow_self] at h
  have e : ∏ i ∈ Finset.univ.erase j, v (qf a (P.updateRow j (∑ k, c k • P k) i)) =
      ∏ i ∈ Finset.univ.erase j, v (qf a (P i)) :=
    Finset.prod_congr rfl fun i hi => by rw [Matrix.updateRow_ne (Finset.ne_of_mem_erase hi)]
  rw [e] at h
  have hR : 0 < ∏ i ∈ Finset.univ.erase j, v (qf a (P i)) :=
    zero_lt_iff.mpr (Finset.prod_ne_zero_iff.mpr fun i _ =>
      (Valuation.ne_zero_iff v).mpr (hrow P hP i))
  have hd : 0 < v P.det ^ 2 := pow_pos (zero_lt_iff.mpr ((Valuation.ne_zero_iff v).mpr hP)) 2
  have hcj : 0 < v (c j) ^ 2 := pow_pos (zero_lt_iff.mpr ((Valuation.ne_zero_iff v).mpr hc)) 2
  rw [map_mul, mul_pow, ← div_div, div_le_div_iff_of_pos_right hd, le_div_iff₀ hcj,
    mul_right_comm, mul_le_mul_iff_left₀ hR, mul_comm] at h
  exact h

lemma exists_three (f : Fin 5 → Bool) :
    ∃ i j k : Fin 5, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧ f j = f i ∧ f k = f i := by
  revert f
  decide

lemma exists_scale (v : Valuation K ℤᵐ⁰) (hv : Function.Surjective v) {x y : K} (hx : x ≠ 0)
    (hy : y ≠ 0)
    (h : decide (Even (WithZero.log (v y))) = decide (Even (WithZero.log (v x)))) :
    ∃ u : K, v u ^ 2 * v y = v x := by
  have he : Even (WithZero.log (v x) - WithZero.log (v y)) := by
    rw [Int.even_sub]
    simpa [eq_comm] using h
  obtain ⟨m, hm⟩ := he
  obtain ⟨u, hu⟩ := hv (WithZero.exp m)
  refine ⟨u, ?_⟩
  rw [hu, ← WithZero.exp_log ((Valuation.ne_zero_iff v).mpr hx),
    ← WithZero.exp_log ((Valuation.ne_zero_iff v).mpr hy), sq, ← WithZero.exp_add,
    ← WithZero.exp_add]
  congr 1
  omega

end FiveVar

open FiveVar in

theorem exists_zero_five_of_valuation {K : Type*} [Field K] (h2 : (2 : K) ≠ 0)
    (v : Valuation K ℤᵐ⁰) (hv : Function.Surjective v)
    (hsq : ∀ x : K, v (x - 1) < v 4 → IsSquare x)
    (hcw : ∀ c : Fin 3 → Fin 3 → K, (∀ i j, v (c i j) ≤ 1) →
      ∃ x : Fin 3 → K, (∀ i, v (x i) ≤ 1) ∧ (∃ i, v (x i) = 1) ∧
        v (∑ i, ∑ j, c i j * x i * x j) < 1)
    (a : Fin 5 → K) : ∃ x : Fin 5 → K, x ≠ 0 ∧ ∑ i, a i * x i ^ 2 = 0 := by
  by_contra hno
  have han : ∀ x, qf a x = 0 → x = 0 := by
    intro x hx
    by_contra h
    exact hno ⟨x, h, hx⟩
  obtain ⟨P, hP, hmin⟩ := exists_basis h2 v hsq a han
  obtain ⟨i, j, k, hij, hik, hjk, hj, hk⟩ :=
    exists_three fun i => decide (Even (WithZero.log (v (qf a (P i)))))
  obtain ⟨s, hs⟩ := exists_scale v hv (hP i) (hP j) hj
  obtain ⟨t, ht⟩ := exists_scale v hv (hP i) (hP k) hk
  set w := qf a (P i) with hw
  have hw0 : w ≠ 0 := hP i
  have hvw : 0 < v w := zero_lt_iff.mpr ((Valuation.ne_zero_iff v).mpr hw0)
  have hq : ∀ x, v (qf a x) = v w → v (qf a x / w) ≤ 1 := by
    intro x hx
    rw [map_div₀, hx, div_self hvw.ne']
  have hb : ∀ x y, v (qf a x) = v w → v (qf a y) = v w → v (bf a x y / w) ≤ 1 := by
    intro x y hx hy
    rw [map_div₀, div_le_one₀ hvw]
    apply le_of_pow_le_pow_left₀ (n := 2) two_ne_zero zero_le'
    have := val_bf_sq_le h2 v hsq a han x y
    rwa [hx, hy, ← sq] at this
  have h0 : v (qf a (P i)) = v w := rfl
  have h1 : v (qf a (s • P j)) = v w := by rw [qf_smul, map_mul, map_pow, hs]
  have h2' : v (qf a (t • P k)) = v w := by rw [qf_smul, map_mul, map_pow, ht]
  obtain ⟨x, -, ⟨l, hl⟩, hx⟩ := hcw
    ![![qf a (P i) / w, bf a (P i) (s • P j) / w, bf a (P i) (t • P k) / w],
      ![0, qf a (s • P j) / w, bf a (s • P j) (t • P k) / w],
      ![0, 0, qf a (t • P k) / w]] (by
      intro p q
      fin_cases p <;> fin_cases q
      · exact hq _ h0
      · exact hb _ _ h0 h1
      · exact hb _ _ h0 h2'
      · simp
      · exact hq _ h1
      · exact hb _ _ h1 h2'
      · simp
      · simp
      · exact hq _ h2')
  set c : Fin 5 → K := Pi.single i (x 0) + Pi.single j (x 1 * s) + Pi.single k (x 2 * t) with hc
  have hsum : ∑ p, c p • P p = x 0 • P i + x 1 • s • P j + x 2 • t • P k := by
    simp only [hc, Pi.add_apply, add_smul, Finset.sum_add_distrib, Pi.single_apply, ite_smul,
      zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true, smul_smul]
  have hlt : v (qf a (∑ p, c p • P p)) < v w := by
    rw [← div_lt_one₀ hvw, ← map_div₀]
    convert hx using 2
    rw [hsum]
    exact qf_three a _ _ _ x w
  fin_cases l
  · have := hmin c i
    have e : c i = x 0 := by simp [hc, hij, hik]
    have hl' : v (x 0) = 1 := hl
    rw [e, hl', one_pow, one_mul] at this
    exact absurd hlt (not_lt.mpr this)
  · have := hmin c j
    have e : c j = x 1 * s := by simp [hc, hij.symm, hjk]
    have hl' : v (x 1) = 1 := hl
    rw [e, map_mul, hl', one_mul, hs] at this
    exact absurd hlt (not_lt.mpr this)
  · have := hmin c k
    have e : c k = x 2 * t := by simp [hc, hik.symm, hjk.symm]
    have hl' : v (x 2) = 1 := hl
    rw [e, map_mul, hl', one_mul, ht] at this
    exact absurd hlt (not_lt.mpr this)

end GlobalTheory.LocalQuad
