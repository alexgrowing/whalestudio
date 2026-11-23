import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {R : Type} [CommRing R]

omit [Fintype ι] in
theorem tpow_diagonal_alg (n : ℕ) (a : ι → R) :
    tpow n (diagonal a) = diagonal (fun b : Fin n → ι => ∏ j, a (b j)) := by
  ext b c
  simp only [tpow, Matrix.of_apply]
  by_cases h : b = c
  · subst h
    simp
  · rw [Matrix.diagonal_apply_ne _ h]
    obtain ⟨j, hj⟩ := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ j) (Matrix.diagonal_apply_ne _ hj)

omit [Fintype ι] in
theorem tpow_one_alg (n : ℕ) : tpow n (1 : Matrix ι ι R) = 1 := by
  have h := tpow_diagonal_alg (ι := ι) n (fun _ => (1 : R))
  simpa using h

omit [DecidableEq ι] in
theorem tpow_mul_alg (n : ℕ) (y z : Matrix ι ι R) : tpow n (y * z) = tpow n y * tpow n z := by
  classical
  ext b c
  simp only [tpow, Matrix.of_apply, Matrix.mul_apply]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.prod_mul_distrib]

theorem act_apply_alg {m : ℕ} (d : Fin m → ℕ) (t : TIdx ι d → R) (y : Matrix ι ι R) (k : TIdx ι d) :
    act d t y k = ∑ a : Fin (d k.1) → ι, t ⟨k.1, a⟩ * ∏ j, y (a j) (k.2 j) := by
  simp [act, tpow, Matrix.vecMul, dotProduct]

end

theorem tpow_act_algebra : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (R : Type) [CommRing R], (∀ n : ℕ, tpow n (1 : Matrix ι ι R) = 1 ∧ (∀ y z : Matrix ι ι R, tpow n (y * z) = tpow n y * tpow n z) ∧ ∀ y : Matrix ι ι R, (tpow n y)ᵀ = tpow n yᵀ) ∧ ∀ (m : ℕ) (d : Fin m → ℕ) (t : TIdx ι d → R), act d t 1 = t ∧ (∀ y z : Matrix ι ι R, act d t (y * z) = act d (act d t y) z) ∧ (∀ (a : ι → R) (k : TIdx ι d), act d t (diagonal a) k = t k * ∏ j, a (k.2 j)) ∧ (∀ (S : Subring R) (y : Matrix ι ι R), (∀ k, t k ∈ S) → (∀ i j, y i j ∈ S) → ∀ k, act d t y k ∈ S) ∧ (∀ (c : R) (y : Matrix ι ι R), act d (c • t) y = c • act d t y) ∧ ∀ (R' : Type) [CommRing R'] (φ : R →+* R') (y : Matrix ι ι R), act d (fun k => φ (t k)) (y.map φ) = fun k => φ (act d t y k) := by
  intro ι _ _ R _
  refine ⟨fun n => ⟨tpow_one_alg n, tpow_mul_alg n, fun y => ?_⟩, fun m d t => ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · ext a b
    simp [tpow]
  · funext k
    simp [act, tpow_one_alg]
  · intro y z
    funext k
    simp only [act, tpow_mul_alg, ← Matrix.vecMul_vecMul]
  · intro a k
    simp only [act, tpow_diagonal_alg, Matrix.vecMul_diagonal]
  · intro S y ht hy k
    rw [act_apply_alg]
    exact S.sum_mem fun a _ => S.mul_mem (ht _) (S.prod_mem fun j _ => hy _ _)
  · intro c y
    funext k
    simp only [act_apply_alg, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]
  · intro R' _ φ y
    funext k
    simp only [act_apply_alg, map_sum, map_mul, map_prod, Matrix.map_apply]

end GlobalTheory.ClassFin
