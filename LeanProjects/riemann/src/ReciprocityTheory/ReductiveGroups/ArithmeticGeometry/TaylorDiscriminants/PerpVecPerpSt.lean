import Mathlib

namespace ReciprocityTheory.ChartRestriction.G.TB

open MvPolynomial

variable {R : Type} [CommRing R]

noncomputable def xForm {p q n : ℕ} (e : Fin p → Fin n → R) (a b : Fin p) :
    MvPolynomial ((Fin p × Fin n) ⊕ (Fin q × Fin n)) R :=
  ∑ k, X (Sum.inl (a, k)) * C (e b k)

noncomputable def yForm {p q n : ℕ} (f : Fin q → Fin n → R) (a b : Fin q) :
    MvPolynomial ((Fin p × Fin n) ⊕ (Fin q × Fin n)) R :=
  ∑ k, X (Sum.inr (a, k)) * C (f b k)

noncomputable def leadMinor {S : Type} [CommRing S] {m : ℕ} (M : Matrix (Fin m) (Fin m) S) (i : Fin (m + 1)) : S :=
  (M.submatrix (Fin.castLE (Nat.lt_succ_iff.mp i.isLt)) (Fin.castLE (Nat.lt_succ_iff.mp i.isLt)) :
    Matrix (Fin i) (Fin i) S).det

noncomputable def detPoly {p q n : ℕ} (e : Fin p → Fin n → R) (f : Fin q → Fin n → R)
    (c : Fin (p + 1) → ℕ) (c' : Fin (q + 1) → ℕ) : MvPolynomial ((Fin p × Fin n) ⊕ (Fin q × Fin n)) R :=
  (∏ i, leadMinor (Matrix.of (xForm (q := q) e)) i ^ c i) *
    ∏ i, leadMinor (Matrix.of (yForm (p := p) f)) i ^ c' i

noncomputable def mixedLap {p q n : ℕ} (a : Fin p) (b : Fin q) :
    MvPolynomial ((Fin p × Fin n) ⊕ (Fin q × Fin n)) R →ₗ[R]
      MvPolynomial ((Fin p × Fin n) ⊕ (Fin q × Fin n)) R :=
  ∑ k, (pderiv (Sum.inl (a, k))).toLinearMap ∘ₗ (pderiv (Sum.inr (b, k))).toLinearMap

def DetPolyHarmSt : Prop :=
  ∀ (R : Type) [CommRing R] (p q n : ℕ) (e : Fin p → Fin n → R) (f : Fin q → Fin n → R)
    (c : Fin (p + 1) → ℕ) (c' : Fin (q + 1) → ℕ),
    (∀ c₀ d₀, ∑ k, e c₀ k * f d₀ k = 0) → ∀ a b, mixedLap a b (detPoly e f c c') = 0

section Perp

variable {V : Type} [AddCommGroup V] [Module R V]

def hMat {p : ℕ} (h : V →ₗ[R] (V → R)) (e e' : Fin p → V) : Matrix (Fin p) (Fin p) R :=
  Matrix.of fun a' a => h (e' a') (e a)

def perpVec {p : ℕ} (h : V →ₗ[R] (V → R)) (e e' : Fin p → V) (g : V) : V :=
  (hMat h e e').det • g - ∑ a, ∑ a', ((hMat h e e').adjugate a a' * h g (e a)) • e' a'

end Perp

def PerpVecSt : Prop :=
  ∀ (R : Type) [CommRing R] (V : Type) [AddCommGroup V] [Module R V] (p : ℕ)
    (h : V →ₗ[R] (V → R)) (e e' : Fin p → V) (g : V) (c : Fin p), h (perpVec h e e' g) (e c) = 0

def PerpVecIntSt : Prop :=
  ∀ (R : Type) [CommRing R] (O : Subring R) (V : Type) [AddCommGroup V] [Module R V] (p : ℕ)
    (h : V →ₗ[R] (V → R)) (L : Submodule O V),
    (∀ u ∈ L, ∀ v ∈ L, h u v ∈ O) → ∀ (e e' : Fin p → V) (g : V),
      (∀ a, e a ∈ L) → (∀ a, e' a ∈ L) → g ∈ L → perpVec h e e' g ∈ L

def PerpVecPerpSt : Prop :=
  ∀ (R : Type) [CommRing R] (V : Type) [AddCommGroup V] [Module R V] (p : ℕ)
    (h : V →ₗ[R] (V → R)) (e e' : Fin p → V) (g : V),
    (∀ a, h g (e a) = 0) → perpVec h e e' g = (hMat h e e').det • g

end ReciprocityTheory.ChartRestriction.G.TB
