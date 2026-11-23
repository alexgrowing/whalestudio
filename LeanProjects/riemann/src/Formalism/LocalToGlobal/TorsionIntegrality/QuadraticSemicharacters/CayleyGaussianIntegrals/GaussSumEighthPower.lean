import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.UnitaryConstant

noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.H

namespace IsQuadFn

variable {M : Type*} [AddCommGroup M] {φ : M → ℂ} {b : M → M → ℂ}

theorem b_eq (h : IsQuadFn φ b) (x y : M) : b x y = φ (x + y) / (φ x * φ y) := by
  exact eq_div_of_mul_eq (mul_ne_zero (h.ne x) (h.ne y)) (by rw [h.add]; ring)

theorem symm (h : IsQuadFn φ b) (x y : M) : b x y = b y x := by
  rw [h.b_eq x y, h.b_eq y x, add_comm, mul_comm (φ x)]

theorem b_ne (h : IsQuadFn φ b) (x y : M) : b x y ≠ 0 := by
  rw [h.b_eq]
  exact div_ne_zero (h.ne _) (mul_ne_zero (h.ne x) (h.ne y))

theorem right (h : IsQuadFn φ b) (x y z : M) : b x (y + z) = b x y * b x z := by
  rw [h.symm x (y + z), h.left, h.symm y x, h.symm z x]

theorem phi_zero (h : IsQuadFn φ b) : φ 0 = 1 := by
  have h0 := h.sq 0 (0 : M)
  simpa using h0

theorem b_zero_left (h : IsQuadFn φ b) (y : M) : b 0 y = 1 := by
  rw [h.b_eq, zero_add, h.phi_zero, one_mul, div_self (h.ne y)]

theorem b_zero_right (h : IsQuadFn φ b) (y : M) : b y 0 = 1 := by
  rw [h.symm, h.b_zero_left]

theorem b_nsmul_left (h : IsQuadFn φ b) (k : ℕ) (x y : M) : b (k • x) y = b x y ^ k := by
  induction k with
  | zero => rw [zero_nsmul, h.b_zero_left, pow_zero]
  | succ k ih => rw [succ_nsmul, h.left, ih, pow_succ]

theorem b_nsmul_nsmul (h : IsQuadFn φ b) (k l : ℕ) (x y : M) :
    b (k • x) (l • y) = b x y ^ (k * l) := by
  rw [h.b_nsmul_left, h.symm x (l • y), h.b_nsmul_left, h.symm y x,
    ← pow_mul, mul_comm l k]

theorem b_neg_left (h : IsQuadFn φ b) (x y : M) : b (-x) y = (b x y)⁻¹ := by
  have h1 : b (-x) y * b x y = 1 := by
    rw [← h.left, show -x + x = (0 : M) by simp, h.b_zero_left]
  exact eq_inv_of_mul_eq_one_left h1

theorem b_neg_right (h : IsQuadFn φ b) (x y : M) : b x (-y) = (b x y)⁻¹ := by
  rw [h.symm x (-y), h.b_neg_left, h.symm y x]

theorem b_self (h : IsQuadFn φ b) (x : M) : b x x = φ x ^ 2 := by
  have hx := h.ne x
  have h1 := h.sq 2 x
  rw [two_nsmul, h.add] at h1
  apply mul_left_cancel₀ (mul_ne_zero hx hx)
  rw [h1]
  ring

theorem phi_neg (h : IsQuadFn φ b) (x : M) : φ (-x) = φ x := by
  have hx := h.ne x
  have h1 := h.add x (-x)
  rw [show x + -x = (0 : M) by simp, h.phi_zero, h.b_neg_right, h.b_self] at h1
  calc φ (-x) = φ (-x) * (φ x ^ 2 * (φ x ^ 2)⁻¹) := by
        rw [mul_inv_cancel₀ (pow_ne_zero 2 hx), mul_one]
    _ = φ x * φ (-x) * (φ x ^ 2)⁻¹ * φ x := by ring
    _ = φ x := by rw [← h1, one_mul]

theorem phi_orth4 (h : IsQuadFn φ b) (x₀ x₁ x₂ x₃ : M) (h01 : b x₀ x₁ = 1) (h02 : b x₀ x₂ = 1)
    (h03 : b x₀ x₃ = 1) (h12 : b x₁ x₂ = 1) (h13 : b x₁ x₃ = 1) (h23 : b x₂ x₃ = 1)
    (k₀ k₁ k₂ k₃ : ℕ) :
    φ (k₀ • x₀ + k₁ • x₁ + k₂ • x₂ + k₃ • x₃)
      = φ x₀ ^ (k₀ ^ 2) * φ x₁ ^ (k₁ ^ 2) * φ x₂ ^ (k₂ ^ 2) * φ x₃ ^ (k₃ ^ 2) := by
  simp only [h.add, h.left, h.b_nsmul_nsmul, h01, h02, h03, h12, h13, h23, one_pow, mul_one,
    h.sq]
  try ring

theorem sum_sq_of_anti {P : Type*} [AddCommGroup P] [Fintype P] {Φ : P → ℂ} {B : P → P → ℂ}
    (h : IsQuadFn Φ B) (T : P →+ P) (hT : ∀ v, Φ v * Φ (T v) = 1) :
    (∑ v, Φ v) ^ 2 = (Fintype.card P : ℂ) := by
  classical
  have hB : ∀ v w, B (T v) (T w) * B v w = 1 := by
    intro v w
    have h1 := hT (v + w)
    rw [map_add, h.add, h.add] at h1
    have h2 := hT v
    have h3 := hT w
    have h4 : (Φ v * Φ (T v)) * (Φ w * Φ (T w)) * (B (T v) (T w) * B v w) = 1 := by
      linear_combination h1
    rwa [h2, h3, one_mul, one_mul] at h4
  have hinj : Function.Injective T := by
    refine (injective_iff_map_eq_zero T).mpr (fun v hv => h.nondeg v (fun w => ?_))
    have h5 := hB v w
    rwa [hv, h.b_zero_left, one_mul] at h5
  have hsurj : Function.Surjective T := Finite.injective_iff_surjective.mp hinj
  have hchar : ∀ w, w ≠ 0 → ∑ v, B w (T v) = 0 := by
    intro w hw
    obtain ⟨u, hu⟩ : ∃ u, B w (T u) ≠ 1 := by
      by_contra hcon
      push Not at hcon
      exact hw (h.nondeg w (fun y => by obtain ⟨u, rfl⟩ := hsurj y; exact hcon u))
    have hs : B w (T u) * ∑ v, B w (T v) = ∑ v, B w (T v) := by
      rw [Finset.mul_sum]
      exact Fintype.sum_equiv (Equiv.addLeft u) _ _ (fun v => by simp [h.right])
    have h6 : (B w (T u) - 1) * ∑ v, B w (T v) = 0 := by
      rw [sub_mul, hs, one_mul, sub_self]
    exact (mul_eq_zero.mp h6).resolve_left (sub_ne_zero.mpr hu)
  have hrow : ∀ v, Φ v * ∑ w, Φ w = ∑ w, Φ w * B w (T v) := by
    intro v
    have e : ∑ w, Φ (w + T v) = ∑ w, Φ w :=
      Fintype.sum_equiv (Equiv.addRight (T v)) _ _ (fun w => by simp)
    rw [← e, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun w _ => ?_)
    rw [h.add]
    linear_combination (Φ w * B w (T v)) * hT v
  have hcol : ∀ w, ∑ v, B w (T v) = if w = 0 then (Fintype.card P : ℂ) else 0 := by
    intro w
    split_ifs with hw
    · subst hw
      simp [h.b_zero_left]
    · exact hchar w hw
  calc (∑ v, Φ v) ^ 2 = ∑ v, Φ v * ∑ w, Φ w := by rw [pow_two, Finset.sum_mul]
    _ = ∑ v, ∑ w, Φ w * B w (T v) := Finset.sum_congr rfl (fun v _ => hrow v)
    _ = ∑ w, Φ w * ∑ v, B w (T v) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun w _ => ?_)
        rw [Finset.mul_sum]
    _ = ∑ w, Φ w * (if w = 0 then (Fintype.card P : ℂ) else 0) :=
        Finset.sum_congr rfl (fun w _ => by rw [hcol w])
    _ = (Fintype.card P : ℂ) := by
        simp [h.phi_zero]

theorem pow4 (h : IsQuadFn φ b) :
    IsQuadFn (fun v : Fin 4 → M => ∏ i, φ (v i)) (fun v w => ∏ i, b (v i) (w i)) where
  add v w := by simp only [Pi.add_apply, h.add, Finset.prod_mul_distrib]
  left u v w := by simp only [Pi.add_apply, h.left, Finset.prod_mul_distrib]
  sq k v := by simp only [Pi.smul_apply, h.sq, Finset.prod_pow]
  ne v := Finset.prod_ne_zero_iff.2 fun i _ => h.ne _
  nondeg v hv := by
    funext i
    apply h.nondeg
    intro y
    have h1 := hv (Pi.single i y)
    rw [Finset.prod_eq_single i] at h1
    · simpa using h1
    · intro j _ hj
      rw [Pi.single_eq_of_ne hj, h.b_zero_right]
    · intro hi
      exact absurd (Finset.mem_univ i) hi

end IsQuadFn

section Quaternion

variable (M : Type*) [AddCommGroup M]

def quatI : (Fin 4 → M) →+ (Fin 4 → M) where
  toFun v := ![-v 1, v 0, -v 3, v 2]
  map_zero' := by ext i; fin_cases i <;> simp
  map_add' v w := by ext i; fin_cases i <;> simp <;> abel

def quatJ : (Fin 4 → M) →+ (Fin 4 → M) where
  toFun v := ![-v 2, v 3, v 0, -v 1]
  map_zero' := by ext i; fin_cases i <;> simp
  map_add' v w := by ext i; fin_cases i <;> simp <;> abel

def quatK : (Fin 4 → M) →+ (Fin 4 → M) where
  toFun v := ![-v 3, -v 2, v 1, v 0]
  map_zero' := by ext i; fin_cases i <;> simp
  map_add' v w := by ext i; fin_cases i <;> simp <;> abel

end Quaternion

private theorem eq_one_of_eq_inv_mul_self_mul_inv_mul_self {a c X : ℂ} (ha : a ≠ 0) (hc : c ≠ 0)
    (hX : X = (a⁻¹ * a) * (c⁻¹ * c)) : X = 1 := by
  rw [hX, inv_mul_cancel₀ ha, inv_mul_cancel₀ hc, one_mul]

theorem gaussSumEighthPower : GaussEighth := by
  intro M _ _ φ b h
  have H := h.pow4
  have hPI : ∀ v : Fin 4 → M, ∏ i, φ (quatI M v i) = ∏ i, φ (v i) := by
    intro v
    simp only [Fin.prod_univ_four]
    change φ (-v 1) * φ (v 0) * φ (-v 3) * φ (v 2) = φ (v 0) * φ (v 1) * φ (v 2) * φ (v 3)
    simp only [h.phi_neg]
    ring
  have hPJ : ∀ v : Fin 4 → M, ∏ i, φ (quatJ M v i) = ∏ i, φ (v i) := by
    intro v
    simp only [Fin.prod_univ_four]
    change φ (-v 2) * φ (v 3) * φ (v 0) * φ (-v 1) = φ (v 0) * φ (v 1) * φ (v 2) * φ (v 3)
    simp only [h.phi_neg]
    ring
  have hPK : ∀ v : Fin 4 → M, ∏ i, φ (quatK M v i) = ∏ i, φ (v i) := by
    intro v
    simp only [Fin.prod_univ_four]
    change φ (-v 3) * φ (-v 2) * φ (v 1) * φ (v 0) = φ (v 0) * φ (v 1) * φ (v 2) * φ (v 3)
    simp only [h.phi_neg]
    ring
  have pI : ∀ v : Fin 4 → M, ∏ i, b (v i) (quatI M v i) = 1 := by
    intro v
    rw [Fin.prod_univ_four]
    change b (v 0) (-v 1) * b (v 1) (v 0) * b (v 2) (-v 3) * b (v 3) (v 2) = 1
    simp only [h.b_neg_left, h.b_neg_right, inv_inv]
    rw [h.symm (v 1) (v 0), h.symm (v 3) (v 2)]
    exact eq_one_of_eq_inv_mul_self_mul_inv_mul_self (h.b_ne (v 0) (v 1)) (h.b_ne (v 2) (v 3)) (by ring)
  have pJ : ∀ v : Fin 4 → M, ∏ i, b (v i) (quatJ M v i) = 1 := by
    intro v
    rw [Fin.prod_univ_four]
    change b (v 0) (-v 2) * b (v 1) (v 3) * b (v 2) (v 0) * b (v 3) (-v 1) = 1
    simp only [h.b_neg_left, h.b_neg_right, inv_inv]
    rw [h.symm (v 2) (v 0), h.symm (v 3) (v 1)]
    exact eq_one_of_eq_inv_mul_self_mul_inv_mul_self (h.b_ne (v 0) (v 2)) (h.b_ne (v 1) (v 3)) (by ring)
  have pK : ∀ v : Fin 4 → M, ∏ i, b (v i) (quatK M v i) = 1 := by
    intro v
    rw [Fin.prod_univ_four]
    change b (v 0) (-v 3) * b (v 1) (-v 2) * b (v 2) (v 1) * b (v 3) (v 0) = 1
    simp only [h.b_neg_left, h.b_neg_right, inv_inv]
    rw [h.symm (v 2) (v 1), h.symm (v 3) (v 0)]
    exact eq_one_of_eq_inv_mul_self_mul_inv_mul_self (h.b_ne (v 0) (v 3)) (h.b_ne (v 1) (v 2)) (by ring)
  have pIJ : ∀ v : Fin 4 → M, ∏ i, b (quatI M v i) (quatJ M v i) = 1 := by
    intro v
    rw [Fin.prod_univ_four]
    change b (-v 1) (-v 2) * b (v 0) (v 3) * b (-v 3) (v 0) * b (v 2) (-v 1) = 1
    simp only [h.b_neg_left, h.b_neg_right, inv_inv]
    rw [h.symm (v 3) (v 0), h.symm (v 2) (v 1)]
    exact eq_one_of_eq_inv_mul_self_mul_inv_mul_self (h.b_ne (v 0) (v 3)) (h.b_ne (v 1) (v 2)) (by ring)
  have pIK : ∀ v : Fin 4 → M, ∏ i, b (quatI M v i) (quatK M v i) = 1 := by
    intro v
    rw [Fin.prod_univ_four]
    change b (-v 1) (-v 3) * b (v 0) (-v 2) * b (-v 3) (v 1) * b (v 2) (v 0) = 1
    simp only [h.b_neg_left, h.b_neg_right, inv_inv]
    rw [h.symm (v 3) (v 1), h.symm (v 2) (v 0)]
    exact eq_one_of_eq_inv_mul_self_mul_inv_mul_self (h.b_ne (v 0) (v 2)) (h.b_ne (v 1) (v 3)) (by ring)
  have pJK : ∀ v : Fin 4 → M, ∏ i, b (quatJ M v i) (quatK M v i) = 1 := by
    intro v
    rw [Fin.prod_univ_four]
    change b (-v 2) (-v 3) * b (v 3) (-v 2) * b (v 0) (v 1) * b (-v 1) (v 0) = 1
    simp only [h.b_neg_left, h.b_neg_right, inv_inv]
    rw [h.symm (v 3) (v 2), h.symm (v 1) (v 0)]
    exact eq_one_of_eq_inv_mul_self_mul_inv_mul_self (h.b_ne (v 0) (v 1)) (h.b_ne (v 2) (v 3)) (by ring)
  obtain ⟨a, c, d, e, habcd⟩ := Nat.sum_four_squares (Fintype.card (Fin 4 → M) ^ 2 - 1)
  have hN : 1 ≤ Fintype.card (Fin 4 → M) ^ 2 :=
    Nat.one_le_iff_ne_zero.mpr (pow_pos (Fintype.card_pos_iff.mpr ⟨0⟩) 2).ne'
  obtain ⟨T, hTdef⟩ : ∃ T : (Fin 4 → M) →+ (Fin 4 → M), ∀ v,
      T v = a • v + c • quatI M v + d • quatJ M v + e • quatK M v :=
    ⟨AddMonoidHom.mk'
      (fun v : Fin 4 → M => a • v + c • quatI M v + d • quatJ M v + e • quatK M v)
      (fun v w => by simp only [map_add, smul_add]; abel), fun v => rfl⟩
  have hT : ∀ v : Fin 4 → M, (∏ i, φ (v i)) * (∏ i, φ (T v i)) = 1 := by
    intro v
    have hO : (∏ i, φ ((a • v + c • quatI M v + d • quatJ M v + e • quatK M v) i))
        = (∏ i, φ (v i)) ^ (a ^ 2) * (∏ i, φ (quatI M v i)) ^ (c ^ 2)
          * (∏ i, φ (quatJ M v i)) ^ (d ^ 2) * (∏ i, φ (quatK M v i)) ^ (e ^ 2) :=
      H.phi_orth4 v (quatI M v) (quatJ M v) (quatK M v)
        (pI v) (pJ v) (pK v) (pIJ v) (pIK v) (pJK v) a c d e
    have hsq : (∏ i, φ ((Fintype.card (Fin 4 → M) • v) i))
        = (∏ i, φ (v i)) ^ (Fintype.card (Fin 4 → M) ^ 2) := H.sq _ v
    rw [card_nsmul_eq_zero] at hsq
    simp only [Pi.zero_apply, h.phi_zero, Finset.prod_const_one] at hsq
    rw [hTdef, hO, hPI, hPJ, hPK, ← pow_add, ← pow_add, ← pow_add, habcd, ← pow_succ',
      Nat.sub_add_cancel hN, ← hsq]
  have key : (∑ v : Fin 4 → M, ∏ i, φ (v i)) ^ 2 = (Fintype.card (Fin 4 → M) : ℂ) :=
    H.sum_sq_of_anti T hT
  have hsum : (∑ x, φ x) ^ 4 = ∑ v : Fin 4 → M, ∏ i, φ (v i) := by
    calc (∑ x, φ x) ^ 4 = ∏ _i : Fin 4, ∑ x, φ x := by simp
      _ = ∑ v : Fin 4 → M, ∏ i, φ (v i) := by
        exact Fintype.prod_sum (fun _ x => φ x)
  rw [show (8 : ℕ) = 4 * 2 by norm_num, pow_mul, hsum, key]
  simp

end Formalism.L2.Th1.H
