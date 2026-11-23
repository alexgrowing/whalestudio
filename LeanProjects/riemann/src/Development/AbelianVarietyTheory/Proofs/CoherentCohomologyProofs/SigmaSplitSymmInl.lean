import Mathlib

namespace GlobalTheory.InnerAutomorphism

section Inner

variable {A : Type*} (R : Type*) [CommSemiring R] [Semiring A] [Algebra R A]

def innerAut (u : Aˣ) : A ≃ₐ[R] A where
  toFun x := (u : A) * x * ((u⁻¹ : Aˣ) : A)
  invFun x := ((u⁻¹ : Aˣ) : A) * x * (u : A)
  left_inv x := by simp [mul_assoc]
  right_inv x := by simp [mul_assoc]
  map_mul' x y := by simp [mul_assoc]
  map_add' x y := by simp [mul_add, add_mul]
  commutes' r := by rw [← Algebra.commutes, mul_assoc, Units.mul_inv, mul_one]

@[simp] theorem innerAut_apply (u : Aˣ) (x : A) :
    innerAut R u x = (u : A) * x * ((u⁻¹ : Aˣ) : A) := rfl

end Inner

section Bounded

variable {K n : Type*} [NormedField K]

def EntriesBounded (M : Matrix n n K) (c : ℝ) : Prop :=
  ∀ i j, ‖M i j‖ ≤ c

theorem EntriesBounded.mono {M : Matrix n n K} {c d : ℝ} (h : EntriesBounded M c)
    (hcd : c ≤ d) : EntriesBounded M d :=
  fun i j => (h i j).trans hcd

theorem EntriesBounded.mul [IsUltrametricDist K] [Fintype n] {M N : Matrix n n K} {c d : ℝ}
    (hM : EntriesBounded M c) (hN : EntriesBounded N d) :
    EntriesBounded (M * N) (c * d) := by
  intro i j
  have hc : 0 ≤ c := (norm_nonneg _).trans (hM i j)
  have hd : 0 ≤ d := (norm_nonneg _).trans (hN i j)
  rw [Matrix.mul_apply]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (mul_nonneg hc hd) ?_
  intro k _
  rw [norm_mul]
  exact mul_le_mul (hM i k) (hN k j) (norm_nonneg _) hc

end Bounded

section DropLast

variable (K : Type*) [Semiring K] (d : ℕ)

def dropLast : (Fin (d + 1) → K) →ₗ[K] (Fin d → K) where
  toFun x i := x i.castSucc
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem dropLast_apply (x : Fin (d + 1) → K) (i : Fin d) :
    dropLast K d x i = x i.castSucc := rfl

end DropLast

section Split

variable {ι : Type*} [DecidableEq ι] (F : ι → Type*)

def sigmaSplit (j : ι) : (Σ i, F i) ≃ F j ⊕ (Σ i : {i // i ≠ j}, F i.1) where
  toFun p := if h : p.1 = j then Sum.inl (h ▸ p.2) else Sum.inr ⟨⟨p.1, h⟩, p.2⟩
  invFun s := Sum.elim (fun x => ⟨j, x⟩) (fun q => ⟨q.1.1, q.2⟩) s
  left_inv := by
    rintro ⟨i, x⟩
    by_cases h : i = j
    · subst h; simp
    · simp [h]
  right_inv := by
    rintro (x | ⟨⟨i, hi⟩, x⟩)
    · simp
    · simp [show ¬ i = j from hi]

theorem sigmaSplit_self (j : ι) (x : F j) : sigmaSplit F j ⟨j, x⟩ = Sum.inl x :=
  (Equiv.apply_eq_iff_eq_symm_apply _).2 rfl

theorem sigmaSplit_of_ne {i j : ι} (h : i ≠ j) (x : F i) :
    sigmaSplit F j ⟨i, x⟩ = Sum.inr ⟨⟨i, h⟩, x⟩ :=
  (Equiv.apply_eq_iff_eq_symm_apply _).2 rfl

end Split

end GlobalTheory.InnerAutomorphism
