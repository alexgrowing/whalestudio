import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ProdEApproxGen

noncomputable section

namespace Formalism.L2.SG.Pf.ProdEApprox

section Mono

variable {A : Type*} [CommRing A] {n : ℕ}

def mono (σ : Fin n → Fin n) (ν : Fin n → A) : Matrix (Fin n) (Fin n) A :=
  Matrix.of fun a b => if b = σ a then ν a else 0

theorem mono_mul (σ : Fin n → Fin n) (ν : Fin n → A) (X : Matrix (Fin n) (Fin n) A) (i j : Fin n) :
    (mono σ ν * X) i j = ν i * X (σ i) j := by
  simp [mono, Matrix.mul_apply, ite_mul]

variable {σ : Fin n → Fin n} (hσ : ∀ a, σ (σ a) = a) (ν : Fin n → A)
include hσ

theorem mul_mono (X : Matrix (Fin n) (Fin n) A) (i j : Fin n) : (X * mono σ ν) i j = X i (σ j) * ν (σ j) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (σ j)]
  · simp [mono, hσ]
  · intro b _ hb
    have hj : j ≠ σ b := fun h => hb (by rw [h, hσ])
    simp [mono, hj]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem fix_entry {l c : Matrix (Fin n) (Fin n) A} (h : l * mono σ ν = mono σ ν * c) (i j : Fin n) :
    l i j * ν j = ν i * c (σ i) (σ j) := by
  have e := congrFun (congrFun h i) (σ j)
  rw [mul_mono hσ, mono_mul, hσ] at e
  exact e

theorem fix_pat (hν : ∀ a, IsUnit (ν a)) {l c : Matrix (Fin n) (Fin n) A} (hc : ∀ i j, j < i → c i j = 0)
    (h : l * mono σ ν = mono σ ν * c) (i j : Fin n) (hij : σ j < σ i) : l i j = 0 := by
  have e := fix_entry hσ ν h i j
  rw [hc _ _ hij, mul_zero] at e
  exact (hν j).mul_left_eq_zero.mp e

omit hσ in

def cOf (σ : Fin n → Fin n) (ν : Fin n → A) (l : Matrix (Fin n) (Fin n) A) : Matrix (Fin n) (Fin n) A :=
  Matrix.of fun a b => Ring.inverse (ν (σ a)) * l (σ a) (σ b) * ν (σ b)

theorem fix_cOf (hν : ∀ a, IsUnit (ν a)) (l : Matrix (Fin n) (Fin n) A) :
    l * mono σ ν = mono σ ν * cOf σ ν l := by
  ext i j
  rw [mul_mono hσ, mono_mul]
  simp only [cOf, Matrix.of_apply, hσ]
  rw [← mul_assoc, ← mul_assoc, Ring.mul_inverse_cancel _ (hν i), one_mul]

theorem cOf_up (l : Matrix (Fin n) (Fin n) A) (hl : ∀ i, l i i = 1) (hpat : ∀ i j, σ j < σ i → l i j = 0)
    (hν : ∀ a, IsUnit (ν a)) : (∀ a, cOf σ ν l a a = 1) ∧ ∀ a b, b < a → cOf σ ν l a b = 0 := by
  refine ⟨fun a => ?_, fun a b hab => ?_⟩
  · simp only [cOf, Matrix.of_apply, hl, mul_one]
    exact Ring.inverse_mul_cancel _ (hν _)
  · simp only [cOf, Matrix.of_apply]
    rw [hpat (σ a) (σ b) (by rw [hσ, hσ]; exact hab), mul_zero, zero_mul]

end Mono

end Formalism.L2.SG.Pf.ProdEApprox
