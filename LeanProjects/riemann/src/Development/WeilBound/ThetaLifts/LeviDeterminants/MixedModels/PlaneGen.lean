import Mathlib

noncomputable section

namespace PositivityTheory.Mix

open Matrix

variable {R : Type} [CommRing R] {n k : ℕ}

def bf (c : R →+* R) (J : Matrix (Fin n) (Fin n) R) (u v : Fin n → R) : R := u ⬝ᵥ J *ᵥ fun i => c (v i)

variable {c : R →+* R} {J : Matrix (Fin n) (Fin n) R}

theorem bf_add_l (u u' v) : bf c J (u + u') v = bf c J u v + bf c J u' v := by
  simp [bf, add_dotProduct]
theorem bf_smul_l (a : R) (u v) : bf c J (a • u) v = a * bf c J u v := by
  simp [bf, smul_dotProduct]
theorem bf_add_r (u v v') : bf c J u (v + v') = bf c J u v + bf c J u v' := by
  have e : (fun i => c ((v + v') i)) = (fun i => c (v i)) + (fun i => c (v' i)) := by
    funext i
    simp
  simp only [bf, e, mulVec_add, dotProduct_add]
theorem bf_smul_r (a : R) (u v) : bf c J u (a • v) = c a * bf c J u v := by
  have e : (fun i => c ((a • v) i)) = c a • (fun i => c (v i)) := by
    funext i
    simp
  simp only [bf, e, mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem bf_mulVec (M : Matrix (Fin n) (Fin n) R) (u v) : bf c J (M *ᵥ u) (M *ᵥ v) = bf c (Mᵀ * J * M.map c) u v := by
  have hc : (fun i => c ((M *ᵥ v) i)) = M.map c *ᵥ fun i => c (v i) := by
    funext i
    simp [mulVec, dotProduct, map_sum, map_mul]
  simp only [bf]
  rw [hc, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec u Mᵀ, vecMul_transpose]

theorem bf_single (i j : Fin n) : bf c J (Pi.single i 1) (Pi.single j 1) = J i j := by
  have e : (fun l => c ((Pi.single j 1 : Fin n → R) l)) = (Pi.single j 1 : Fin n → R) := by
    funext l
    by_cases hl : l = j
    · subst hl
      simp
    · simp [Pi.single_apply, hl]
  simp only [bf, e, mulVec_single_one, single_one_dotProduct]
  rfl

structure PlaneOK (c : R →+* R) (J : Matrix (Fin n) (Fin n) R) (ε : R) (x y : Fin n → R) (ι : Matrix (Fin n) (Fin k) R) : Prop where
  cc : ∀ a, c (c a) = a
  ee : ε * ε = 1
  ce : c ε = ε
  herm : ∀ i j, c (J j i) = ε * J i j
  xx : bf c J x x = 0
  yy : bf c J y y = 0
  xy : bf c J x y = 1
  ix : ∀ z, bf c J (ι *ᵥ z) x = 0
  iy : ∀ z, bf c J (ι *ᵥ z) y = 0
  span : ∀ v, ∃ (s t : R) (z : Fin k → R), v = s • x + ι *ᵥ z + t • y
  nd : ∀ v, (∀ w, bf c J v w = 0) → v = 0

namespace PlaneOK

variable {ε : R} {x y : Fin n → R} {ι : Matrix (Fin n) (Fin k) R} (h : PlaneOK c J ε x y ι)
include h

theorem symm (u v) : bf c J v u = ε * c (bf c J u v) := by
  simp only [bf, dotProduct, mulVec, map_sum, map_mul, Finset.mul_sum, h.cc]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [h.herm]
  linear_combination (-(v i * J i j * c (u j))) * h.ee

theorem yx : bf c J y x = ε := by rw [h.symm, h.xy, map_one, mul_one]
theorem xi (z) : bf c J x (ι *ᵥ z) = 0 := by rw [h.symm, h.ix, map_zero, mul_zero]
theorem yi (z) : bf c J y (ι *ᵥ z) = 0 := by rw [h.symm, h.iy, map_zero, mul_zero]

theorem ext {A B : Matrix (Fin n) (Fin n) R} (hx : A *ᵥ x = B *ᵥ x) (hy : A *ᵥ y = B *ᵥ y)
    (hi : ∀ z, A *ᵥ (ι *ᵥ z) = B *ᵥ (ι *ᵥ z)) : A = B := by
  have hv : ∀ v, A *ᵥ v = B *ᵥ v := by
    intro v
    obtain ⟨s, t, z, rfl⟩ := h.span v
    simp only [mulVec_add, mulVec_smul, hx, hy, hi]
  ext i j
  have e := congrFun (hv (Pi.single j 1)) i
  simpa [mulVec_single_one] using e

omit h in

def lev (c : R →+* R) (J : Matrix (Fin n) (Fin n) R) (ε : R) (x y : Fin n → R) (t s : R) : Matrix (Fin n) (Fin n) R :=
  1 + (t - 1) • vecMulVec x (J *ᵥ fun i => c (y i)) + ((s - 1) * ε) • vecMulVec y (J *ᵥ fun i => c (x i))

omit h in
theorem lev_apply (t s : R) (v) : lev c J ε x y t s *ᵥ v = v + ((t - 1) * bf c J v y) • x + ((s - 1) * ε * bf c J v x) • y := by
  have vm : ∀ p q w : Fin n → R, vecMulVec p q *ᵥ w = (q ⬝ᵥ w) • p := by
    intro p q w
    ext i
    simp only [vecMulVec, mulVec, dotProduct, of_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  simp only [lev, add_mulVec, one_mulVec, smul_mulVec, vm, smul_smul]
  rw [dotProduct_comm (J *ᵥ fun i => c (y i)) v, dotProduct_comm (J *ᵥ fun i => c (x i)) v]
  rfl

theorem levi_element_fixes_first_vector (t s : R) : lev c J ε x y t s *ᵥ x = t • x := by
  rw [lev_apply, h.xy, h.xx]
  simp only [mul_one, mul_zero, zero_smul, add_zero]
  rw [sub_smul, one_smul]
  abel
theorem lev_y (t s : R) : lev c J ε x y t s *ᵥ y = s • y := by
  rw [lev_apply, h.yy, h.yx]
  have e : (s - 1) * ε * ε = s - 1 := by rw [mul_assoc, h.ee, mul_one]
  rw [e]
  simp only [mul_zero, zero_smul, add_zero]
  rw [sub_smul, one_smul]
  abel
theorem lev_i (t s : R) (z) : lev c J ε x y t s *ᵥ (ι *ᵥ z) = ι *ᵥ z := by
  rw [lev_apply, h.iy, h.ix]
  simp

theorem lev_mul {t t' s s' : R} (h1 : t * t' = 1) (h2 : s * s' = 1) : lev c J ε x y t s * lev c J ε x y t' s' = 1 := by
  apply h.ext
  · rw [← mulVec_mulVec, h.levi_element_fixes_first_vector, mulVec_smul, h.levi_element_fixes_first_vector, smul_smul, mul_comm, h1, one_smul, one_mulVec]
  · rw [← mulVec_mulVec, h.lev_y, mulVec_smul, h.lev_y, smul_smul, mul_comm, h2, one_smul, one_mulVec]
  · intro z
    rw [← mulVec_mulVec, h.lev_i, h.lev_i, one_mulVec]

theorem lev_unit {t s : R} (h1 : t * c s = 1) : (lev c J ε x y t s)ᵀ * J * (lev c J ε x y t s).map c = J := by
  have hcs : s * c t = 1 := by
    have e := congrArg c h1
    rw [map_mul, h.cc, map_one] at e
    rw [mul_comm]
    exact e
  have key : ∀ u v, bf c J (lev c J ε x y t s *ᵥ u) (lev c J ε x y t s *ᵥ v) = bf c J u v := by
    intro u v
    obtain ⟨a, b, z, rfl⟩ := h.span u
    obtain ⟨a', b', z', rfl⟩ := h.span v
    simp only [mulVec_add, mulVec_smul, h.levi_element_fixes_first_vector, h.lev_y, h.lev_i, bf_add_l, bf_add_r, bf_smul_l, bf_smul_r,
      h.xx, h.yy, h.xy, h.yx, h.ix, h.iy, h.xi, h.yi, map_mul, smul_smul]
    linear_combination (a * c b') * h1 + (b * c a' * ε) * hcs
  ext i j
  have e := key (Pi.single i 1) (Pi.single j 1)
  rw [bf_mulVec, bf_single, bf_single] at e
  exact e

theorem exists_lev (t : Rˣ) : ∃ m : GL (Fin n) R, m.1ᵀ * J * m.1.map c = J ∧ m.1 *ᵥ x = t.1 • x ∧ m.1 *ᵥ y = c (t⁻¹).1 • y ∧
    ∀ z, m.1 *ᵥ (ι *ᵥ z) = ι *ᵥ z := by
  have hc1 : c (t⁻¹ : Rˣ).1 * c t.1 = 1 := by rw [← map_mul, Units.inv_mul, map_one]
  have hc2 : c t.1 * c (t⁻¹ : Rˣ).1 = 1 := by rw [← map_mul, Units.mul_inv, map_one]
  refine ⟨⟨lev c J ε x y t.1 (c (t⁻¹ : Rˣ).1), lev c J ε x y (t⁻¹ : Rˣ).1 (c t.1),
    h.lev_mul (Units.mul_inv t) hc1, h.lev_mul (Units.inv_mul t) hc2⟩, ?_, h.levi_element_fixes_first_vector _ _, h.lev_y _ _, fun z => h.lev_i _ _ z⟩
  apply h.lev_unit
  rw [h.cc, Units.mul_inv]

end PlaneOK

end PositivityTheory.Mix
