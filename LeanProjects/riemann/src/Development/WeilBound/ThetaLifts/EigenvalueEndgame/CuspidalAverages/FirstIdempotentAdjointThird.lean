import Mathlib

noncomputable section

set_option linter.unusedSectionVars false

namespace PositivityTheory.ThKEnd.Cusp

open Matrix

variable {R n ι : Type} [CommRing R] [Fintype n] [DecidableEq n] [Fintype ι] [DecidableEq ι] {c : R →+* R}
  {J x y x' y' : Matrix n n R} {u u' : Matrix n ι R}

def Adj (c : R →+* R) (J x y : Matrix n n R) : Prop := xᵀ * J = J * y.map c

theorem Adj.one : Adj c J 1 1 := by simp [Adj, Matrix.map_one _ (map_zero c) (map_one c)]

theorem Adj.add (h : Adj c J x y) (h' : Adj c J x' y') : Adj c J (x + x') (y + y') := by
  rw [Adj, transpose_add, Matrix.add_mul, h, h', Matrix.map_add _ (map_add c), Matrix.mul_add]

theorem Adj.sub (h : Adj c J x y) (h' : Adj c J x' y') : Adj c J (x - x') (y - y') := by
  rw [Adj, transpose_sub, Matrix.sub_mul, h, h', Matrix.map_sub _ (map_sub c), Matrix.mul_sub]

theorem Adj.mul (h : Adj c J x y) (h' : Adj c J x' y') : Adj c J (x * x') (y' * y) := by
  rw [Adj, transpose_mul, Matrix.mul_assoc, h, ← Matrix.mul_assoc, h', Matrix.map_mul, Matrix.mul_assoc]

theorem Adj.unit (h : Adj c J x y) (e : y * x = 1) : xᵀ * J * x.map c = J := by
  rw [h, Matrix.mul_assoc, ← Matrix.map_mul, e, Matrix.map_one _ (map_zero c) (map_one c), Matrix.mul_one]

theorem Adj.of_unit (h : xᵀ * J * x.map c = J) (e : x * y = 1) : Adj c J x y := by
  unfold Adj
  conv_rhs => rw [← h]
  rw [Matrix.mul_assoc, ← Matrix.map_mul, e, Matrix.map_one _ (map_zero c) (map_one c), Matrix.mul_one]

structure Fr (c : R →+* R) (J : Matrix n n R) (u u' : Matrix n ι R) : Prop where
  cc : ∀ r, c (c r) = r
  sk : (J.map c)ᵀ = -J
  uu : uᵀ * J * u.map c = 0
  vv : u'ᵀ * J * u'.map c = 0
  uv : uᵀ * J * u'.map c = 1

def row (c : R →+* R) (J : Matrix n n R) (u : Matrix n ι R) : Matrix ι n R := (J * u.map c)ᵀ

theorem map_map_c {a b : Type} (h : ∀ r, c (c r) = r) (z : Matrix a b R) : (z.map c).map c = z := by
  ext i j; exact h _

namespace Fr

variable (h : Fr c J u u')
include h

theorem row_c (w : Matrix n ι R) : (row c J w).map c = -(wᵀ * J) := by
  rw [row, transpose_map, Matrix.map_mul, map_map_c h.cc, transpose_mul, h.sk, Matrix.mul_neg]

theorem vu : row c J u' * u = 1 := by
  rw [row, ← transpose_transpose u, ← transpose_mul, ← Matrix.mul_assoc, h.uv, transpose_one]

theorem vv' : row c J u' * u' = 0 := by
  rw [row]; nth_rw 2 [← transpose_transpose u']
  rw [← transpose_mul, ← Matrix.mul_assoc, h.vv, transpose_zero]

theorem uu' : row c J u * u = 0 := by
  rw [row]; nth_rw 2 [← transpose_transpose u]
  rw [← transpose_mul, ← Matrix.mul_assoc, h.uu, transpose_zero]

theorem uv' : row c J u * u' = -1 := by
  rw [← map_map_c h.cc (row c J u * u'), Matrix.map_mul, h.row_c, Matrix.neg_mul, h.uv, Matrix.map_neg _ (map_neg c),
    Matrix.map_one _ (map_zero c) (map_one c)]

theorem adj (w w' : Matrix n ι R) (g : Matrix ι ι R) : Adj c J (w * g * row c J w') (-(w' * (g.map c)ᵀ * row c J w)) := by
  rw [Adj, Matrix.map_neg _ (map_neg c), Matrix.map_mul, Matrix.map_mul, h.row_c, transpose_map, map_map_c h.cc, row]
  simp only [transpose_mul, transpose_transpose, Matrix.mul_neg, neg_neg, Matrix.mul_assoc]

end Fr

def e1 (c : R →+* R) (J : Matrix n n R) (u u' : Matrix n ι R) : Matrix n n R := u * row c J u'

def e3 (c : R →+* R) (J : Matrix n n R) (u u' : Matrix n ι R) : Matrix n n R := -(u' * row c J u)

def lv (c : R →+* R) (J : Matrix n n R) (u u' : Matrix n ι R) (g g' : Matrix ι ι R) : Matrix n n R :=
  1 + u * (g - 1) * row c J u' - u' * (g' - 1) * row c J u

def mid (c : R →+* R) (J : Matrix n n R) (u u' : Matrix n ι R) (s : Matrix n n R) : Matrix n n R :=
  e1 c J u u' + (1 - e1 c J u u' - e3 c J u u') * s * (1 - e1 c J u u' - e3 c J u u') + e3 c J u u'

namespace Fr

variable (h : Fr c J u u')
include h

theorem lv_u (g g' : Matrix ι ι R) : lv c J u u' g g' * u = u * g := by
  simp only [lv, Matrix.sub_mul, Matrix.add_mul, Matrix.mul_assoc, h.vu, h.uu', Matrix.mul_one, Matrix.one_mul, Matrix.mul_zero,
    Matrix.mul_sub]
  abel

theorem lv_v (g g' : Matrix ι ι R) : lv c J u u' g g' * u' = u' * g' := by
  simp only [lv, Matrix.sub_mul, Matrix.add_mul, Matrix.mul_assoc, h.vv', h.uv', Matrix.mul_one, Matrix.one_mul, Matrix.mul_zero,
    Matrix.mul_sub, Matrix.mul_neg]
  abel

theorem v_lv (g g' : Matrix ι ι R) : row c J u' * lv c J u u' g g' = g * row c J u' := by
  simp only [lv, Matrix.mul_sub, Matrix.mul_add, ← Matrix.mul_assoc, h.vu, h.vv', Matrix.mul_one, Matrix.one_mul, Matrix.zero_mul,
    Matrix.sub_mul]
  abel

theorem u_lv (g g' : Matrix ι ι R) : row c J u * lv c J u u' g g' = g' * row c J u := by
  simp only [lv, Matrix.mul_sub, Matrix.mul_add, ← Matrix.mul_assoc, h.uu', h.uv', Matrix.mul_one, Matrix.one_mul, Matrix.zero_mul,
    Matrix.sub_mul, Matrix.neg_mul]
  abel

theorem lv_mul (g g' k k' : Matrix ι ι R) : lv c J u u' g g' * lv c J u u' k k' = lv c J u u' (g * k) (g' * k') := by
  conv_lhs => enter [1]; rw [lv]
  rw [Matrix.sub_mul, Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_assoc _ (row c J u), h.v_lv, h.u_lv, Matrix.one_mul]
  simp only [lv, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, Matrix.one_mul, Matrix.mul_one]
  abel

theorem lv_adj (g g' : Matrix ι ι R) : Adj c J (lv c J u u' g g') (lv c J u u' (g'.map c)ᵀ (g.map c)ᵀ) := by
  have e : ∀ g : Matrix ι ι R, ((g - 1).map c)ᵀ = (g.map c)ᵀ - 1 := fun g => by
    rw [Matrix.map_sub _ (map_sub c), Matrix.map_one _ (map_zero c) (map_one c), transpose_sub, transpose_one]
  have := (Adj.one.add (h.adj u u' (g - 1))).sub (h.adj u' u (g' - 1))
  rw [e, e] at this
  rw [show lv c J u u' (g'.map c)ᵀ (g.map c)ᵀ = 1 + -(u' * ((g.map c)ᵀ - 1) * row c J u) - -(u * ((g'.map c)ᵀ - 1) * row c J u') by
    rw [lv]; abel]
  exact this

theorem first_idempotent_commute_levi (g g' : Matrix ι ι R) : e1 c J u u' * lv c J u u' g g' = lv c J u u' g g' * e1 c J u u' := by
  rw [e1, Matrix.mul_assoc, h.v_lv, ← Matrix.mul_assoc (lv c J u u' g g'), h.lv_u, Matrix.mul_assoc]

theorem third_idempotent_commute_levi (g g' : Matrix ι ι R) : e3 c J u u' * lv c J u u' g g' = lv c J u u' g g' * e3 c J u u' := by
  rw [e3, Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc, h.u_lv, ← Matrix.mul_assoc (lv c J u u' g g'), h.lv_v, Matrix.mul_assoc]

theorem lv_mid (g g' : Matrix ι ι R) :
    lv c J u u' g g' * (1 - e1 c J u u' - e3 c J u u') = 1 - e1 c J u u' - e3 c J u u' := by
  rw [e1, e3, Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_neg, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h.lv_u, h.lv_v]
  simp only [lv, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]
  abel

theorem e11 : e1 c J u u' * e1 c J u u' = e1 c J u u' := by
  rw [e1, Matrix.mul_assoc, ← Matrix.mul_assoc _ u, h.vu, Matrix.one_mul]

theorem e13 : e1 c J u u' * e3 c J u u' = 0 := by
  simp [e1, e3, Matrix.mul_assoc, ← Matrix.mul_assoc _ u', h.vv']

theorem e31 : e3 c J u u' * e1 c J u u' = 0 := by
  simp [e1, e3, Matrix.mul_assoc, ← Matrix.mul_assoc _ u, h.uu']

theorem e33 : e3 c J u u' * e3 c J u u' = e3 c J u u' := by
  simp [e3, Matrix.mul_assoc, ← Matrix.mul_assoc _ u', h.uv']

theorem first_idempotent_adjoint_third : Adj c J (e1 c J u u') (e3 c J u u') := by
  simpa [e1, e3, Matrix.map_one _ (map_zero c) (map_one c)] using h.adj u u' 1

theorem third_idempotent_adjoint_first : Adj c J (e3 c J u u') (e1 c J u u') := by
  have := (Adj.one.sub Adj.one).sub (h.adj u' u 1)
  simpa [e1, e3, Matrix.map_one _ (map_zero c) (map_one c)] using this

theorem row_mul {s s' : Matrix n n R} (hs : Adj c J s s') {g : Matrix ι ι R} (e : s' * u = u * g) :
    row c J u * s = (g.map c)ᵀ * row c J u := by
  rw [row, ← transpose_transpose s, ← transpose_mul, ← Matrix.mul_assoc, hs, Matrix.mul_assoc, ← Matrix.map_mul, e,
    Matrix.map_mul, ← Matrix.mul_assoc, transpose_mul]

theorem mid_adj {s s' : Matrix n n R} (hs : Adj c J s s') : Adj c J (mid c J u u' s) (mid c J u u' s') := by
  have q := (Adj.one.sub h.first_idempotent_adjoint_third).sub h.third_idempotent_adjoint_first
  have := (h.first_idempotent_adjoint_third.add ((q.mul hs).mul q)).add h.third_idempotent_adjoint_first
  rw [sub_right_comm 1 (e3 c J u u'), ← Matrix.mul_assoc] at this
  rw [show mid c J u u' s' = e3 c J u u' + (1 - e1 c J u u' - e3 c J u u') * s' * (1 - e1 c J u u' - e3 c J u u') + e1 c J u u' by
    rw [mid]; abel]
  exact this

theorem mid_mul {s s' : Matrix n n R} (a : s * e1 c J u u' = e1 c J u u') (b : e3 c J u u' * s' = e3 c J u u') :
    mid c J u u' (s * s') = mid c J u u' s * mid c J u u' s' := by
  have h11 := h.e11
  have h13 := h.e13
  have h31 := h.e31
  have h33 := h.e33
  rw [mid, mid, mid]
  generalize e1 c J u u' = p at *
  generalize e3 c J u u' = r at *
  have q1 : (1 - p - r) * p = 0 := by simp [Matrix.sub_mul, h11, h31]
  have q2 : (1 - p - r) * r = 0 := by simp [Matrix.sub_mul, h13, h33]
  have q3 : p * (1 - p - r) = 0 := by simp [Matrix.mul_sub, h11, h13]
  have q4 : r * (1 - p - r) = 0 := by simp [Matrix.mul_sub, h31, h33]
  have q5 : (1 - p - r) * (1 - p - r) = 1 - p - r := by
    nth_rw 1 [Matrix.sub_mul, Matrix.sub_mul, q3, q4]; simp
  have q6 : (1 - p - r) * s * (1 - p - r) * s' * (1 - p - r) = (1 - p - r) * (s * s') * (1 - p - r) := by
    nth_rw 2 [Matrix.mul_sub]
    rw [Matrix.mul_sub _ 1, Matrix.mul_assoc _ s p, a, q1, Matrix.sub_mul, Matrix.sub_mul _ _ s', Matrix.sub_mul,
      Matrix.mul_assoc _ r s', b, Matrix.mul_assoc _ r, q4]
    simp [Matrix.mul_assoc]
  generalize 1 - p - r = q at *
  have a1 : q * s * q * p = 0 := by rw [Matrix.mul_assoc, q1, Matrix.mul_zero]
  have a2 : q * s * q * r = 0 := by rw [Matrix.mul_assoc, q2, Matrix.mul_zero]
  simp only [Matrix.add_mul, Matrix.mul_add, ← Matrix.mul_assoc, h11, h13, h31, h33, q3, q4, a1, a2, Matrix.zero_mul, add_zero, zero_add]
  rw [Matrix.mul_assoc (q * s) q q, q5, q6, Matrix.mul_assoc q s s']

theorem mid_one : mid c J u u' 1 = 1 := by
  have h11 := h.e11
  have h13 := h.e13
  have h31 := h.e31
  have h33 := h.e33
  simp only [mid, Matrix.mul_one, Matrix.mul_sub, Matrix.sub_mul, Matrix.one_mul, h11, h13, h31, h33]
  abel

theorem mid_lv (g g' k k' : Matrix ι ι R) (s : Matrix n n R) :
    mid c J u u' (lv c J u u' g g' * s * lv c J u u' k k') = mid c J u u' s := by
  have : (1 - e1 c J u u' - e3 c J u u') * lv c J u u' g g' = 1 - e1 c J u u' - e3 c J u u' := by
    conv_rhs => rw [← h.lv_mid g g']
    simp only [Matrix.sub_mul, Matrix.mul_sub, h.first_idempotent_commute_levi, h.third_idempotent_commute_levi, Matrix.one_mul, Matrix.mul_one]
  rw [mid, mid, ← Matrix.mul_assoc, ← Matrix.mul_assoc, this, Matrix.mul_assoc _ (lv c J u u' k k'), h.lv_mid]

theorem first_idempotent_mul_vector : e1 c J u u' * u = u := by rw [e1, Matrix.mul_assoc, h.vu, Matrix.mul_one]

theorem third_idempotent_mul_vector : e3 c J u u' * u = 0 := by rw [e3, Matrix.neg_mul, Matrix.mul_assoc, h.uu', Matrix.mul_zero, neg_zero]

theorem q_u : (1 - e1 c J u u' - e3 c J u u') * u = 0 := by simp [Matrix.sub_mul, h.first_idempotent_mul_vector, h.third_idempotent_mul_vector]

theorem u_q : row c J u * (1 - e1 c J u u' - e3 c J u u') = 0 := by
  simp [Matrix.mul_sub, Matrix.mul_add, e1, e3, ← Matrix.mul_assoc, h.uu', h.uv']

theorem qq : (1 - e1 c J u u' - e3 c J u u') * (1 - e1 c J u u' - e3 c J u u') = 1 - e1 c J u u' - e3 c J u u' := by
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_one, h.e11, h.e13, h.e31, h.e33]
  abel

theorem mid_u (s : Matrix n n R) : mid c J u u' s * u = u := by
  simp only [mid, Matrix.add_mul, Matrix.mul_assoc, h.q_u, h.first_idempotent_mul_vector, h.third_idempotent_mul_vector, Matrix.mul_zero, add_zero]

theorem mid_mid (s : Matrix n n R) : mid c J u u' (mid c J u u' s) = mid c J u u' s := by
  have q1 : (1 - e1 c J u u' - e3 c J u u') * e1 c J u u' = 0 := by simp [Matrix.sub_mul, h.e11, h.e31]
  have q2 : (1 - e1 c J u u' - e3 c J u u') * e3 c J u u' = 0 := by simp [Matrix.sub_mul, h.e13, h.e33]
  conv_lhs => rw [mid, mid, Matrix.mul_add, Matrix.mul_add, q1, q2, zero_add, add_zero, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h.qq,
    Matrix.mul_assoc _ _ (1 - _ - _), h.qq]
  rfl

theorem mid_iff (s : Matrix n n R) :
    mid c J u u' s = 1 ↔ (1 - e1 c J u u' - e3 c J u u') * (s - 1) * (1 - e1 c J u u' - e3 c J u u') = 0 := by
  rw [Matrix.mul_sub _ s, Matrix.sub_mul _ (_ * 1), Matrix.mul_one, h.qq, mid, sub_eq_zero]
  constructor <;> intro e
  · rw [← e]; nth_rw 1 [e]; nth_rw 1 [e]; abel
  · rw [e]; abel

theorem move {s s' : Matrix n n R} (hs : Adj c J s s') (a : s * u = u) (a' : s' * u = u) (b : mid c J u u' s = 1) :
    (s - 1) * (1 - e3 c J u u') = u * (row c J u' * (s - 1) * (1 - e3 c J u u')) := by
  have h1 : (s - 1) * e1 c J u u' = 0 := by rw [e1, ← Matrix.mul_assoc, Matrix.sub_mul, a, Matrix.one_mul, sub_self, Matrix.zero_mul]
  have h2 : e3 c J u u' * (s - 1) = 0 := by
    have := h.row_mul hs (g := 1) (by rw [a', Matrix.mul_one])
    rw [Matrix.map_one _ (map_zero c) (map_one c), transpose_one, Matrix.one_mul] at this
    rw [e3, Matrix.neg_mul, Matrix.mul_assoc, Matrix.mul_sub, this, Matrix.mul_one, sub_self, Matrix.mul_zero, neg_zero]
  have h3 := (h.mid_iff s).1 b
  rw [sub_right_comm 1 (e1 c J u u'), Matrix.mul_sub _ (1 - _), Matrix.mul_assoc _ _ (e1 c J u u'), h1, Matrix.mul_zero, sub_zero,
    Matrix.sub_mul, Matrix.sub_mul 1, h2, Matrix.one_mul, sub_zero, Matrix.sub_mul, sub_eq_zero] at h3
  rw [h3, e1]
  conv_rhs => rw [Matrix.mul_assoc, h3, e1]
  simp only [← Matrix.mul_assoc]
  rw [Matrix.mul_assoc u _ u, h.vu, Matrix.mul_one]

end Fr

theorem lv_one : lv c J u u' 1 1 = 1 := by simp [lv]

theorem exists_dual {K : Type} [Field K] [CharZero K] {c : K →+* K} (cc : ∀ r, c (c r) = r) {J : Matrix n n K} (sk : (J.map c)ᵀ = -J)
    (hJ : J.det ≠ 0) {u : Matrix n ι K} (hu : Function.Injective u.mulVec) (uu : uᵀ * J * u.map c = 0) : ∃ u', Fr c J u u' := by
  obtain ⟨L, hL⟩ := u.mulVecLin.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.2 hu)
  have h1 : LinearMap.toMatrix' L * u = 1 := by
    rw [← LinearMap.toMatrix'_toLin' u, ← LinearMap.toMatrix'_comp, Matrix.toLin'_apply', hL, LinearMap.toMatrix'_id]
  set w := (J⁻¹ * (LinearMap.toMatrix' L)ᵀ).map c with hw
  have h2 : uᵀ * J * w.map c = 1 := by
    rw [hw, map_map_c cc, Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hJ.isUnit, ← transpose_mul, h1, transpose_one]
  have k : ∀ a b : Matrix n ι K, ((aᵀ * J * b.map c).map c)ᵀ = -(bᵀ * J * a.map c) := fun a b => by
    rw [Matrix.map_mul, Matrix.map_mul, map_map_c cc, transpose_mul, transpose_mul, sk, transpose_map, transpose_transpose]
    simp [Matrix.mul_assoc]
  have h3 : wᵀ * J * u.map c = -1 := by
    have := k u w
    rw [h2, Matrix.map_one _ (map_zero c) (map_one c), transpose_one] at this
    exact neg_eq_iff_eq_neg.1 this.symm
  set S := wᵀ * J * w.map c with hS
  have h4 : ((2 : K)⁻¹ • Sᵀ).map c = (2 : K)⁻¹ • -S := by
    rw [hS, ← k w w, ← hS]
    ext i j
    simp [map_ofNat]
  refine ⟨w - u * ((2 : K)⁻¹ • Sᵀ), cc, sk, uu, ?_, ?_⟩
  · rw [Matrix.map_sub _ (map_sub c), Matrix.map_mul, h4, transpose_sub, transpose_mul, Matrix.sub_mul, Matrix.sub_mul,
      Matrix.mul_sub, Matrix.mul_sub, ← hS, ← Matrix.mul_assoc (wᵀ * J), h3, Matrix.mul_assoc _ uᵀ, Matrix.mul_assoc _ (uᵀ * J), h2,
      Matrix.mul_assoc _ (uᵀ * J), ← Matrix.mul_assoc (uᵀ * J), uu]
    ext i j
    simp
    ring
  · rw [Matrix.map_sub _ (map_sub c), Matrix.map_mul, Matrix.mul_sub, h2, ← Matrix.mul_assoc, uu, Matrix.zero_mul, sub_zero]

end PositivityTheory.ThKEnd.Cusp

end
