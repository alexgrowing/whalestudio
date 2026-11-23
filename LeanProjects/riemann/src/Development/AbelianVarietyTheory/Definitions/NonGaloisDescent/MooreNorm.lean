import Mathlib

noncomputable section

namespace GlobalTheory.PMonE

open Finset

section Basic

variable {F : Type*} [NormedField F] {m : Type*} [Fintype m]

def Integral (x : m → F) : Prop := ∀ i, ‖x i‖ ≤ 1

def gsum (q D : ℕ) (M : ℕ → Matrix m m F) (x : m → F) : m → F :=
  ∑ n ∈ range (D + 1), (M n).mulVec (fun i => x i ^ q ^ n)

variable [DecidableEq m]

structure Normal (N : ℕ) (M : ℕ → Matrix m m F) : Prop where
  int : ∀ n i j, ‖M n i j‖ ≤ 1
  top : M N = 1
  small : ∀ n, N < n → ∀ i j, ‖M n i j‖ < 1

end Basic

def GLOnto (N : ℕ) : Prop :=
  ∀ (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] [CompleteSpace F] [IsAlgClosed F]
    (p : ℕ) [Fact p.Prime] [CharP F p] (m : Type) [Fintype m] [DecidableEq m] (e D : ℕ), 0 < e → N ≤ D →
    ∀ M : ℕ → Matrix m m F, Normal N M → ∀ b : m → F, Integral b →
      ∃ x : m → F, Integral x ∧ gsum (p ^ e) D M x = b

def GLCount (N : ℕ) : Prop :=
  ∀ (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] [CompleteSpace F] [IsAlgClosed F]
    (p : ℕ) [Fact p.Prime] [CharP F p] (m : Type) [Fintype m] [DecidableEq m] (e D : ℕ), 0 < e → N ≤ D →
    ∀ M : ℕ → Matrix m m F, Normal N M → (M 0).det ≠ 0 →
      Nat.card {x : m → F // Integral x ∧ gsum (p ^ e) D M x = 0} = (p ^ e) ^ (Fintype.card m * N)

section Win

variable {F : Type*} [NormedField F] (p : ℕ) [Fact p.Prime] [CharP F p] [PerfectRing F p]

def pw (k : ℤ) (x : F) : F :=
  if 0 ≤ k then x ^ p ^ k.toNat else ((frobeniusEquiv F p).symm)^[(-k).toNat] x

def Orth {h : ℕ} (lam : Fin h → F) : Prop :=
  ∀ (c : Fin h → ℤ) (j : Fin h), ¬ (p : ℤ) ∣ c j → ‖lam j‖ ≤ ‖∑ i, (c i : F) * lam i‖

def term {h : ℕ} (ϖ : F) (lam : Fin h → F) (x : Fin h → F) (r j : Fin h) (n : ℤ) : F :=
  lam j * ϖ ^ (-n) * pw p ((r : ℤ) + n * h) (x j)

def rowT {h : ℕ} (ϖ : F) (lam : Fin h → F) (K : ℕ) (x : Fin h → F) (r : Fin h) : F :=
  ∑ j, ∑ n ∈ Icc (-(K : ℤ)) K, term p ϖ lam x r j n

end Win

def MooreNorm : Prop :=
  ∀ (F : Type) [NormedField F] [IsUltrametricDist F] (p : ℕ) [Fact p.Prime] [CharP F p] [PerfectRing F p] (h : ℕ)
    (lam : Fin h → F), Antitone (fun j => ‖lam j‖) → Orth p lam →
    ‖(Matrix.of fun r j : Fin h => lam j ^ p ^ (r : ℕ)).det‖ = ∏ j : Fin h, ‖lam j‖ ^ p ^ (h - 1 - (j : ℕ))

def WinThm : Prop :=
  ∀ (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] [CompleteSpace F] [IsAlgClosed F] (p : ℕ) [Fact p.Prime]
    [CharP F p] [PerfectRing F p] (h : ℕ) (ϖ : F), 0 < h → ‖ϖ‖ = (p : ℝ)⁻¹ → ∀ lam : Fin h → F, (∀ j, lam j ≠ 0) →
    Antitone (fun j => ‖lam j‖) → Orth p lam → (∀ i j, ‖lam i‖ < p * ‖lam j‖) →
    ∃ (ρ τ : Fin h → ℝ) (K : ℕ), (∀ j, 0 < ρ j ∧ ρ j < 1) ∧ (∀ r, 0 < τ r) ∧
      (∀ x : Fin h → F, (∀ j, ‖x j‖ ≤ ρ j) → ∀ (r j : Fin h) (n : ℤ),
        ‖term p ϖ lam x r j n‖ ≤ τ r ∧ ((K : ℤ) < |n| → ‖term p ϖ lam x r j n‖ ≤ τ r / p)) ∧
      (∀ b : Fin h → F, (∀ r, ‖b r‖ ≤ τ r) → ∃ x : Fin h → F, (∀ j, ‖x j‖ ≤ ρ j) ∧ ∀ r, rowT p ϖ lam K x r = b r) ∧
      (∃ x : Fin h → F, (∀ j, ‖x j‖ ≤ ρ j) ∧ (∃ j, ρ j ^ p ^ h < ‖x j‖) ∧ ∀ r, rowT p ϖ lam K x r = 0)

end GlobalTheory.PMonE

end
