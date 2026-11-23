import Mathlib

noncomputable section

open Matrix

namespace Formalism.IndefR.LocBrg.Witt

variable {R : Type} [CommRing R]

def cTr (σ : R →+* R) {m p : Type} (M : Matrix m p R) : Matrix p m R := (M.map σ)ᵀ

def hq (σ : R →+* R) {m : Type} [Fintype m] (H : Matrix m m R) (x : m → R) : R :=
  ∑ a, ∑ b, σ (x a) * H a b * x b

def IsDiagU {m : Type} (M : Matrix m m R) : Prop := (∀ i j, i ≠ j → M i j = 0) ∧ ∀ i, IsUnit (M i i)

def blk0 {n : ℕ} (c : R) (M : Matrix (Fin n) (Fin n) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
  Matrix.of (Fin.cons (Fin.cons c fun _ => 0) fun i => Fin.cons 0 (M i))

@[simp] theorem corner_block_zero_zero {n : ℕ} (c : R) (M : Matrix (Fin n) (Fin n) R) : blk0 c M 0 0 = c := rfl
@[simp] theorem corner_block_zero_succ {n : ℕ} (c : R) (M : Matrix (Fin n) (Fin n) R) (j : Fin n) :
    blk0 c M 0 j.succ = 0 := rfl
@[simp] theorem corner_block_succ_zero {n : ℕ} (c : R) (M : Matrix (Fin n) (Fin n) R) (i : Fin n) :
    blk0 c M i.succ 0 = 0 := rfl
@[simp] theorem corner_block_succ_succ {n : ℕ} (c : R) (M : Matrix (Fin n) (Fin n) R) (i j : Fin n) :
    blk0 c M i.succ j.succ = M i j := rfl

section Local

variable [IsLocalRing R]

variable (σ : R →+* R) (hσ : ∀ x, σ (σ x) = x)

end Local

section Main

variable [IsLocalRing R] (σ : R →+* R)

def colE {n : ℕ} (x : Fin (n + 1) → R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
  Matrix.of fun a b => Fin.cases (x a) (fun b' => (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) R) a b'.succ) b

def gsR {n : ℕ} (u : R) (m : Fin n → R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
  Matrix.of (Fin.cons (Fin.cons 1 fun j => -(u * m j)) fun i => Fin.cons 0 ((1 : Matrix (Fin n) (Fin n) R) i))

@[simp] theorem gsR_zero_zero {n : ℕ} (u : R) (m : Fin n → R) : gsR u m 0 0 = 1 := rfl
@[simp] theorem gsR_zero_succ {n : ℕ} (u : R) (m : Fin n → R) (j : Fin n) : gsR u m 0 j.succ = -(u * m j) := rfl
@[simp] theorem gsR_succ_zero {n : ℕ} (u : R) (m : Fin n → R) (i : Fin n) : gsR u m i.succ 0 = 0 := rfl
@[simp] theorem gsR_succ_succ {n : ℕ} (u : R) (m : Fin n → R) (i j : Fin n) :
    gsR u m i.succ j.succ = (1 : Matrix (Fin n) (Fin n) R) i j := rfl

end Main

section Anti

variable [IsLocalRing R] (σ : R →+* R)

def antiJR (n : ℕ) : Matrix (Fin n) (Fin n) R := Matrix.of fun i j => if i = Fin.rev j then 1 else 0

def sq {m : Type} [Fintype m] (x y : m → R) : R := ∑ a, σ (x a) * y a

end Anti

section Anti2

variable [IsLocalRing R] (σ : R →+* R)

def colQ {n : ℕ} (t h : R) (b : Fin n) : Fin n → R :=
  if b = Fin.rev b then Pi.single b 1
  else if b.val < (Fin.rev b).val then Pi.single b 1 + Pi.single (Fin.rev b) t
  else Pi.single (Fin.rev b) h + Pi.single b (-(t * h))

end Anti2

section Anti3

variable [IsLocalRing R] (σ : R →+* R)

def matQ {n : ℕ} (t h : R) : Matrix (Fin n) (Fin n) R := Matrix.of fun a b => colQ t h b a

end Anti3

end Formalism.IndefR.LocBrg.Witt
