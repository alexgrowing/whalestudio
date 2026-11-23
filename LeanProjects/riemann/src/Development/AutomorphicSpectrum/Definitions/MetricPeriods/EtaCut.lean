import Mathlib

namespace GlobalTheory.CompanionTheory.Ar.ThA

open scoped Matrix ComplexConjugate

noncomputable section

abbrev Low (n : ℕ) : Type := {p : Fin n × Fin n // p.2 < p.1}

def lowU {n : ℕ} (z : Low n → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun a b => if h : b < a then z ⟨(a, b), h⟩ else if a = b then 1 else 0

def lmin {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (i : Fin (n + 1)) : ℂ :=
  (M.submatrix (Fin.castLE (Nat.le_of_lt_succ i.isLt)) (Fin.castLE (Nat.le_of_lt_succ i.isLt))).det

def gramA {n : ℕ} (A x y : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  xᵀ * A * y.map conj

def Jp (n p : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.diagonal fun a : Fin n => if (a : ℕ) < p then 1 else -1

def sqn {n : ℕ} (z : Low n → ℂ) : ℝ := ∑ e, ‖z e‖ ^ 2

def densA {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (z : Low n → ℂ) : ℝ :=
  ∏ i : Fin n, ‖lmin (gramA A (lowU z) (lowU z)) i.castSucc‖ ^ (-2 : ℤ)

def etaCut {W : Type} [NormedAddCommGroup W] (χ : ℝ → ℝ) (r0 δ : ℝ) (v : W) : ℝ :=
  χ (‖v‖ ^ 2 / r0 ^ 2) * Real.log ((‖v‖ ^ 2 / r0 ^ 2 + δ) / 2)

def IsCut (χ : ℝ → ℝ) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) χ ∧ (∀ t, 0 ≤ χ t ∧ χ t ≤ 1) ∧ (∀ t, t ≤ 1 / 4 → χ t = 1) ∧
    (∀ t, 97 / 100 ≤ t → χ t = 0) ∧ (∀ t, |deriv χ t| ≤ 3) ∧ ∀ t, |deriv (deriv χ) t| ≤ 30

end

end GlobalTheory.CompanionTheory.Ar.ThA
