import Mathlib

noncomputable section

open Classical
open scoped BigOperators

namespace GlobalTheory.FinWeil

variable {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M]

structure IsHeis (σ : R →+* R) (w : R) (γ : X → X → ℂ) (W : X → M →ₗ[ℂ] M) : Prop where
  sg_sg : ∀ r, σ (σ r) = r
  w_add : w + σ w = 1
  add_left : ∀ x y z, γ (x + y) z = γ x z * γ y z
  add_right : ∀ x y z, γ x (y + z) = γ x y * γ x z
  alt : ∀ x, γ x x = 1
  adj : ∀ r x y, γ (r • x) y = γ x (σ r • y)
  zero : ∀ v, W 0 v = v
  comp : ∀ x y v, W x (W y v) = γ (w • x) y • W (x + y) v

def SelfDual (γ : X → X → ℂ) (A : Submodule R X) : Prop := ∀ x, x ∈ A ↔ ∀ a ∈ A, γ x a = 1

def Fixes (W : X → M →ₗ[ℂ] M) (A : Submodule R X) (v : M) : Prop := ∀ a ∈ A, W a v = v

def idx (A B : Submodule R X) : ℕ := A.toAddSubgroup.relIndex B.toAddSubgroup

def sumOp (W : X → M →ₗ[ℂ] M) (A B : Submodule R X) (v : M) : M :=
  ∑ᶠ q : B.toAddSubgroup ⧸ A.toAddSubgroup.addSubgroupOf B.toAddSubgroup, W ((Quotient.out q : B.toAddSubgroup) : X) v

def normOp (lam : ℕ →* ℂ) (W : X → M →ₗ[ℂ] M) (A B : Submodule R X) (v : M) : M :=
  (lam (idx A B))⁻¹ • sumOp W A B v

def GoodNorm (σ : R →+* R) (lam : ℕ →* ℂ) : Prop :=
  (∀ n, n ≠ 0 → lam n ≠ 0) ∧ ∀ P : Ideal R, P.IsMaximal → Finite (R ⧸ P) →
    lam (Nat.card (R ⧸ P)) ^ 2 = (Nat.card (R ⧸ P) : ℂ) ∧
    ((∀ r ∈ P, σ r ∈ P) → lam (Nat.card (R ⧸ P)) = -(Real.sqrt (Nat.card (R ⧸ P)) : ℂ) ∧ ∃ r, σ r - r ∉ P)

def Adj (A B : Submodule R X) : Prop :=
  ∃ x ∈ B, ∃ P : Ideal R, P.IsMaximal ∧ Finite (R ⧸ P) ∧ (∀ r : R, r • x ∈ A ↔ r ∈ P) ∧ B ≤ (A ⊓ B) ⊔ Submodule.span R {x}

namespace IsHeis

variable {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M} (h : IsHeis σ w γ W)
include h

theorem skew (x y : X) : γ x y * γ y x = 1 := by
  have h1 := h.alt (x + y)
  rw [h.add_left, h.add_right, h.add_right, h.alt, h.alt] at h1
  simpa using h1

theorem ne_zero (x y : X) : γ x y ≠ 0 := left_ne_zero_of_mul_eq_one (h.skew x y)

theorem zero_left (y : X) : γ 0 y = 1 := by
  have h1 := h.add_left 0 0 y
  rw [add_zero] at h1
  exact (mul_eq_left₀ (h.ne_zero 0 y)).1 h1.symm

theorem zero_right (x : X) : γ x 0 = 1 := by
  have h1 := h.add_right x 0 0
  rw [add_zero] at h1
  exact (mul_eq_left₀ (h.ne_zero x 0)).1 h1.symm

theorem neg_left (x y : X) : γ (-x) y = (γ x y)⁻¹ := by
  have h1 := h.add_left (-x) x y
  rw [neg_add_cancel, h.zero_left] at h1
  exact eq_inv_of_mul_eq_one_left h1.symm

theorem neg_right (x y : X) : γ x (-y) = (γ x y)⁻¹ := by
  have h1 := h.add_right x (-y) y
  rw [neg_add_cancel, h.zero_right] at h1
  exact eq_inv_of_mul_eq_one_left h1.symm

theorem swap (x y : X) : γ y x = (γ x y)⁻¹ := eq_inv_of_mul_eq_one_right (h.skew x y)

theorem swap_eq_one {x y : X} (hxy : γ x y = 1) : γ y x = 1 := by rw [h.swap, hxy, inv_one]

theorem nsmul_left (n : ℕ) (x y : X) : γ (n • x) y = γ x y ^ n := by
  induction n with
  | zero => simp [h.zero_left]
  | succ n ih => rw [succ_nsmul, h.add_left, ih, pow_succ]

theorem nsmul_right (n : ℕ) (x y : X) : γ x (n • y) = γ x y ^ n := by
  induction n with
  | zero => simp [h.zero_right]
  | succ n ih => rw [succ_nsmul, h.add_right, ih, pow_succ]

theorem comm (x y : X) (v : M) : W x (W y v) = γ x y • W y (W x v) := by
  have h1 : γ (w • x) y = γ x y * γ (w • y) x := by
    have h2 : γ x y = γ (w • x) y * γ (σ w • x) y := by rw [← h.add_left, ← add_smul, h.w_add, one_smul]
    rw [h2, h.adj (σ w), h.sg_sg, mul_assoc, h.skew, mul_one]
  rw [h.comp, h.comp, smul_smul, h1, add_comm]

theorem iso {A : Submodule R X} (hA : SelfDual γ A) {x y : X} (hx : x ∈ A) (hy : y ∈ A) : γ x y = 1 := (hA x).1 hx y hy

theorem comp_of_mem {A : Submodule R X} (hA : SelfDual γ A) {x y : X} (hx : x ∈ A) (hy : y ∈ A) (v : M) :
    W x (W y v) = W (x + y) v := by
  rw [h.comp, h.iso hA (A.smul_mem w hx) hy, one_smul]

theorem neg_comp (x : X) (v : M) : W (-x) (W x v) = γ (w • -x) x • v := by
  rw [h.comp, neg_add_cancel, h.zero]

end IsHeis

theorem isHeis_trivial (σ : R →+* R) (w : R) (h1 : ∀ r, σ (σ r) = r) (h2 : w + σ w = 1) :
    IsHeis σ w (fun _ _ : X => (1 : ℂ)) (fun _ => (LinearMap.id : M →ₗ[ℂ] M)) :=
  ⟨h1, h2, by simp, by simp, by simp, by simp, by simp, by simp⟩

end GlobalTheory.FinWeil
