import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAdmissibleIntegralBasisChangeOne

set_option autoImplicit false

noncomputable section

open Polynomial

namespace GlobalTheory.Nef

def symMat {R : Type} [CommRing R] (m : ℕ) (A : Matrix (Fin 2) (Fin 2) R) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) R :=
  Matrix.of fun a i => ((C (A 0 1) + C (A 1 1) * X) ^ (i : ℕ) * C (A 0 0) ^ (m - i)).coeff a

theorem symMat_mulVec {R : Type} [CommRing R] (m : ℕ) (A : Matrix (Fin 2) (Fin 2) R)
    (p : Fin (m + 1) → R) :
    (symMat m A).mulVec p = fun a =>
      (∑ i : Fin (m + 1), C (p i) * (C (A 0 1) + C (A 1 1) * X) ^ (i : ℕ) * C (A 0 0) ^ (m - i)).coeff a := by
  funext a
  simp only [Matrix.mulVec, dotProduct, symMat, Matrix.of_apply, finset_sum_coeff]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_assoc, coeff_C_mul, mul_comm]

theorem symMat_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (m : ℕ)
    (A : Matrix (Fin 2) (Fin 2) R) : (symMat m A).map f = symMat m (A.map f) := by
  ext a i
  simp only [symMat, Matrix.map_apply, Matrix.of_apply]
  rw [← Polynomial.coeff_map]
  simp [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_add]

def twistAt {k F : Type} [Field k] [Field F] [Algebra k F] {n : ℕ} (v₀ : Place k F) (c : F)
    (h : Place k F → Matrix (Fin n) (Fin n) F) : Place k F → Matrix (Fin n) (Fin n) F := by
  classical
  exact fun v => if v = v₀ then c • h v else h v

theorem twistAt_self {k F : Type} [Field k] [Field F] [Algebra k F] {n : ℕ} (v₀ : Place k F) (c : F)
    (h : Place k F → Matrix (Fin n) (Fin n) F) : twistAt v₀ c h v₀ = c • h v₀ := by
  simp [twistAt]

theorem twistAt_of_ne {k F : Type} [Field k] [Field F] [Algebra k F] {n : ℕ} (v₀ : Place k F) (c : F)
    (h : Place k F → Matrix (Fin n) (Fin n) F) (v : Place k F) (hv : v ≠ v₀) :
    twistAt v₀ c h v = h v := by
  simp [twistAt, hv]

end GlobalTheory.Nef
