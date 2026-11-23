import Mathlib
import Formalism.PeriodIntegrals.SmithMat

namespace PI.SmithWork

open Matrix

variable {R : Type*} [CommRing R]

section General

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def Eqv (A B : Matrix ι ι R) : Prop :=
  ∃ U V : Matrix ι ι R, IsUnit U ∧ IsUnit V ∧ U * A * V = B

theorem Eqv.refl (A : Matrix ι ι R) : Eqv A A :=
  ⟨1, 1, isUnit_one, isUnit_one, by simp⟩

theorem Eqv.trans {A B C : Matrix ι ι R} (h₁ : Eqv A B) (h₂ : Eqv B C) : Eqv A C := by
  obtain ⟨U, V, hU, hV, rfl⟩ := h₁
  obtain ⟨U', V', hU', hV', rfl⟩ := h₂
  exact ⟨U' * U, V * V', hU'.mul hU, hV.mul hV', by simp only [Matrix.mul_assoc]⟩

theorem Eqv.mul_left {A B U : Matrix ι ι R} (h : Eqv A B) (hU : IsUnit U) : Eqv A (U * B) :=
  h.trans ⟨U, 1, hU, isUnit_one, by simp⟩

theorem Eqv.mul_right {A B V : Matrix ι ι R} (h : Eqv A B) (hV : IsUnit V) : Eqv A (B * V) :=
  h.trans ⟨1, V, isUnit_one, hV, by simp⟩

theorem isUnit_of_mul_eq_one {A B : Matrix ι ι R} (h : A * B = 1) : IsUnit A :=
  (Matrix.isUnit_iff_isUnit_det A).2 (Matrix.isUnit_det_of_right_inverse h)

theorem isUnit_one_add_vecMulVec (u v : ι → R) (h : v ⬝ᵥ u = 0) :
    IsUnit (1 + vecMulVec u v) := by
  have hT : vecMulVec u v * vecMulVec u v = 0 := by
    rw [vecMulVec_mul_vecMulVec, h]; ext; simp [vecMulVec_apply]
  apply isUnit_of_mul_eq_one (B := 1 - vecMulVec u v)
  rw [add_mul, mul_sub, mul_sub, hT]; simp

theorem addRow_apply (t : ι → R) (i : ι) (B : Matrix ι ι R) (a c : ι) :
    ((1 + vecMulVec t (Pi.single i 1)) * B) a c = B a c + t a * B i c := by
  rw [add_mul, one_mul, vecMulVec_mul, single_one_vecMul]
  simp [vecMulVec_apply]

theorem addCol_apply (s : ι → R) (i : ι) (B : Matrix ι ι R) (a c : ι) :
    (B * (1 + vecMulVec (Pi.single i 1) s)) a c = B a c + B a i * s c := by
  rw [mul_add, mul_one, mul_vecMulVec, mulVec_single_one]
  simp [vecMulVec_apply]

def two (i j : ι) (p q r s : R) : Matrix ι ι R := fun a =>
  if a = i then p • Pi.single i 1 + q • Pi.single j 1
  else if a = j then r • Pi.single i 1 + s • Pi.single j 1
  else Pi.single a 1

end General

section Block

variable {n : ℕ}

def blk (b : R) (D : Matrix (Fin n) (Fin n) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
  fun a c => Fin.cases (Fin.cases b (fun _ => 0) c) (fun i => Fin.cases 0 (fun k => D i k) c) a

@[simp] theorem blk_zero_zero (b : R) (D : Matrix (Fin n) (Fin n) R) : blk b D 0 0 = b := rfl
@[simp] theorem blk_zero_succ (b : R) (D : Matrix (Fin n) (Fin n) R) (k : Fin n) :
    blk b D 0 k.succ = 0 := rfl
@[simp] theorem blk_succ_zero (b : R) (D : Matrix (Fin n) (Fin n) R) (i : Fin n) :
    blk b D i.succ 0 = 0 := rfl
@[simp] theorem blk_succ_succ (b : R) (D : Matrix (Fin n) (Fin n) R) (i k : Fin n) :
    blk b D i.succ k.succ = D i k := rfl

theorem blk_mul (b b' : R) (D D' : Matrix (Fin n) (Fin n) R) :
    blk b D * blk b' D' = blk (b * b') (D * D') := by
  ext a c
  refine Fin.cases ?_ (fun i => ?_) a <;> refine Fin.cases ?_ (fun k => ?_) c <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ]

theorem blk_one : blk (1 : R) (1 : Matrix (Fin n) (Fin n) R) = 1 := by
  ext a c
  refine Fin.cases ?_ (fun i => ?_) a <;> refine Fin.cases ?_ (fun k => ?_) c <;>
    simp [Matrix.one_apply, Fin.succ_ne_zero, (Fin.succ_ne_zero _).symm]

theorem isUnit_blk_one {U : Matrix (Fin n) (Fin n) R} (hU : IsUnit U) : IsUnit (blk 1 U) := by
  obtain ⟨u, rfl⟩ := hU
  apply isUnit_of_mul_eq_one (B := blk 1 (↑u⁻¹ : Matrix (Fin n) (Fin n) R))
  rw [blk_mul, one_mul, Units.mul_inv, blk_one]

theorem eq_blk (B : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (hr : ∀ k : Fin n, B 0 k.succ = 0)
    (hc : ∀ i : Fin n, B i.succ 0 = 0) :
    B = blk (B 0 0) (B.submatrix Fin.succ Fin.succ) := by
  ext a c
  refine Fin.cases ?_ (fun i => ?_) a <;> refine Fin.cases ?_ (fun k => ?_) c <;>
    simp [hr, hc]

theorem Eqv.blk {D D' : Matrix (Fin n) (Fin n) R} (h : Eqv D D') (b : R) :
    Eqv (blk b D) (blk b D') := by
  obtain ⟨U, V, hU, hV, rfl⟩ := h
  exact ⟨_, _, isUnit_blk_one hU, isUnit_blk_one hV, by simp [blk_mul]⟩

end Block

end PI.SmithWork
