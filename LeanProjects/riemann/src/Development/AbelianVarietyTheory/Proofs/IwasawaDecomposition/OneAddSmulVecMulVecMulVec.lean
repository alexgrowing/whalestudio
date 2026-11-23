import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegersAlt

namespace GlobalTheory.UnipKill

noncomputable section

open ReciprocityTheory.ChartRestriction.G.FD NumberField

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ}

theorem cc_add (x y : E) : cc (x + y) = cc x + cc y := map_add _ _ _
theorem cc_sub (x y : E) : cc (x - y) = cc x - cc y := map_sub _ _ _
theorem cc_mul (x y : E) : cc (x * y) = cc x * cc y := map_mul _ _ _
theorem cc_neg (x : E) : cc (-x) = -cc x := map_neg _ _
theorem cc_inv (x : E) : cc x⁻¹ = (cc x)⁻¹ := map_inv₀ _ _
theorem cc_one : cc (1 : E) = 1 := map_one _
theorem cc_zero : cc (0 : E) = 0 := map_zero _
theorem cc_natCast (n : ℕ) : cc (n : E) = n := map_natCast _ _
theorem cc_intCast (n : ℤ) : cc (n : E) = n := map_intCast _ _
theorem cc_two : cc (2 : E) = 2 := by simpa using cc_natCast (E := E) 2
theorem cc_cc (x : E) : cc (cc x) = x := IsCMField.complexConj_apply_apply E x
theorem cc_sum {ι : Type*} (s : Finset ι) (f : ι → E) : cc (∑ i ∈ s, f i) = ∑ i ∈ s, cc (f i) :=
  map_sum _ _ _
theorem cc_pow (x : E) (n : ℕ) : cc (x ^ n) = cc x ^ n := map_pow _ _ _
theorem cc_ofInt (x : 𝓞 E) : cc (x : E) = IsCMField.ringOfIntegersComplexConj E x := rfl

section herm

variable (G : Matrix (Fin N) (Fin N) E)

theorem herm_add_left (x x' y : Fin N → E) : herm G (x + x') y = herm G x y + herm G x' y := by
  simp only [herm, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem herm_add_right (x y y' : Fin N → E) : herm G x (y + y') = herm G x y + herm G x y' := by
  simp only [herm, Pi.add_apply, cc_add, mul_add, Finset.sum_add_distrib]

theorem herm_smul_left (c : E) (x y : Fin N → E) : herm G (c • x) y = c * herm G x y := by
  simp only [herm, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

theorem herm_smul_right (c : E) (x y : Fin N → E) : herm G x (c • y) = cc c * herm G x y := by
  simp only [herm, Pi.smul_apply, smul_eq_mul, cc_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

theorem herm_neg_left (x y : Fin N → E) : herm G (-x) y = - herm G x y := by
  rw [show -x = (-1 : E) • x by simp, herm_smul_left]; ring

theorem herm_neg_right (x y : Fin N → E) : herm G x (-y) = - herm G x y := by
  rw [show -y = (-1 : E) • y by simp, herm_smul_right, cc_neg, cc_one]; ring

theorem herm_sub_left (x x' y : Fin N → E) : herm G (x - x') y = herm G x y - herm G x' y := by
  rw [sub_eq_add_neg, herm_add_left, herm_neg_left, sub_eq_add_neg]

theorem herm_sub_right (x y y' : Fin N → E) : herm G x (y - y') = herm G x y - herm G x y' := by
  rw [sub_eq_add_neg, herm_add_right, herm_neg_right, sub_eq_add_neg]

theorem herm_zero_right (x : Fin N → E) : herm G x 0 = 0 := by simp [herm, cc_zero]

theorem cc_herm (hG : ∀ a b, cc (G a b) = G b a) (x y : Fin N → E) :
    cc (herm G x y) = herm G y x := by
  simp only [herm, cc_sum, cc_mul, cc_cc, hG]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

theorem herm_single (x : Fin N → E) (b : Fin N) :
    herm G x (Pi.single b 1) = ∑ a, x a * G a b := by
  simp [herm, Pi.single_apply, apply_ite cc, cc_one, cc_zero, mul_ite, Finset.sum_ite_eq']

theorem eq_zero_of_herm (hG : G.det ≠ 0) (x : Fin N → E) (h : ∀ y, herm G x y = 0) : x = 0 := by
  have h1 : Matrix.vecMul x G = 0 := by
    ext b
    have := h (Pi.single b 1)
    rw [herm_single] at this
    simpa [Matrix.vecMul, dotProduct] using this
  have hu : IsUnit G := (Matrix.isUnit_iff_isUnit_det G).2 (isUnit_iff_ne_zero.2 hG)
  have := Matrix.vecMul_injective_of_isUnit hu (a₁ := x) (a₂ := 0)
  simpa using this (by simpa using h1)

end herm

def rk1 (G : Matrix (Fin N) (Fin N) E) (u v : Fin N → E) : Matrix (Fin N) (Fin N) E :=
  Matrix.of fun a b => u a * ∑ k, G b k * cc (v k)

theorem one_add_smul_vecMulVec_mulVec (G : Matrix (Fin N) (Fin N) E) (u v x : Fin N → E) :
    (rk1 G u v).mulVec x = herm G x v • u := by
  ext a
  simp only [Matrix.mulVec, dotProduct, rk1, Matrix.of_apply, herm, Pi.smul_apply, smul_eq_mul,
    Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun k _ => by ring

theorem one_add_smul_vecMulVec_mul (G : Matrix (Fin N) (Fin N) E) (u v u' v' : Fin N → E) :
    rk1 G u v * rk1 G u' v' = herm G u' v • rk1 G u v' := by
  rw [Matrix.ext_iff_mulVec]; intro x
  rw [← Matrix.mulVec_mulVec, one_add_smul_vecMulVec_mulVec, one_add_smul_vecMulVec_mulVec, herm_smul_left, Matrix.smul_mulVec,
    one_add_smul_vecMulVec_mulVec, smul_smul, mul_comm]

theorem rk1_smul_left (G : Matrix (Fin N) (Fin N) E) (c : E) (u v : Fin N → E) :
    rk1 G (c • u) v = c • rk1 G u v := by
  ext a b; simp [rk1]; ring

theorem rk1_smul_right (G : Matrix (Fin N) (Fin N) E) (c : E) (u v : Fin N → E) :
    rk1 G u (c • v) = cc c • rk1 G u v := by
  ext a b; simp [rk1, cc_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => by ring

theorem transvMat_eq (G : Matrix (Fin N) (Fin N) E) (ξ : Fin N → E) (α : E) :
    transvMat G ξ α = 1 + α • rk1 G ξ ξ := by
  ext a b; simp [transvMat, rk1, Matrix.one_apply]; ring

def IsIsom (G : Matrix (Fin N) (Fin N) E) (A : Matrix (Fin N) (Fin N) E) : Prop :=
  ∀ x y, herm G (A.mulVec x) (A.mulVec y) = herm G x y

def IsSkew (G : Matrix (Fin N) (Fin N) E) (A : Matrix (Fin N) (Fin N) E) : Prop :=
  ∀ x y, herm G (A.mulVec x) y = - herm G x (A.mulVec y)

variable (G : Matrix (Fin N) (Fin N) E)

theorem herm_mulVec_mulVec_eq_zero {A : Matrix (Fin N) (Fin N) E} (hA : IsSkew G A)
    (h2 : A * A = 0) (x y : Fin N → E) : herm G (A.mulVec x) (A.mulVec y) = 0 := by
  rw [hA, Matrix.mulVec_mulVec, h2]; simp [herm_zero_right]

theorem isSkew_sub_one {A : Matrix (Fin N) (Fin N) E} (hA : IsIsom G A) (h2 : (A - 1) * (A - 1) = 0) :
    IsSkew G (A - 1) := by
  intro x y
  have hinv : A * (1 - (A - 1)) = 1 := by
    have : A * (1 - (A - 1)) = 1 - (A - 1) * (A - 1) := by noncomm_ring
    rw [this, h2, sub_zero]
  have key : herm G (A.mulVec x) y = herm G x ((1 - (A - 1)).mulVec y) := by
    conv_rhs => rw [← hA x ((1 - (A - 1)).mulVec y), Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
  simp only [Matrix.sub_mulVec, Matrix.one_mulVec, herm_sub_left, herm_sub_right, key]
  ring

theorem one_add_pow_of_sq_eq_zero {n : Matrix (Fin N) (Fin N) E} (h2 : n * n = 0) (k : ℕ) :
    (1 + n) ^ k = 1 + (k : E) • n := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih, add_mul, one_mul, mul_add, mul_one, smul_mul_assoc, h2, smul_zero, add_zero,
      Nat.cast_succ, add_smul, one_smul]
    abel

theorem transvMat_mul_transvMat (ξ ξ' : Fin N → E) (h : herm G ξ' ξ = 0) (α β : E) :
    transvMat G ξ α * transvMat G ξ' β = 1 + (α • rk1 G ξ ξ + β • rk1 G ξ' ξ') := by
  rw [transvMat_eq, transvMat_eq, add_mul, one_mul, mul_add, mul_one, smul_mul_assoc, mul_smul_comm,
    one_add_smul_vecMulVec_mul, h, zero_smul, smul_zero, smul_zero]
  abel

theorem transvMat_mul_self (ξ : Fin N → E) (h : herm G ξ ξ = 0) (α β : E) :
    transvMat G ξ α * transvMat G ξ β = transvMat G ξ (α + β) := by
  rw [transvMat_mul_transvMat G ξ ξ h, transvMat_eq, add_smul]

theorem transvMat_pow (ξ : Fin N → E) (h : herm G ξ ξ = 0) (α : E) (k : ℕ) :
    transvMat G ξ α ^ k = transvMat G ξ (k * α) := by
  induction k with
  | zero => simp [transvMat_eq]
  | succ k ih => rw [pow_succ, ih, transvMat_mul_self G ξ h, Nat.cast_succ]; congr 1; ring

end

end GlobalTheory.UnipKill
