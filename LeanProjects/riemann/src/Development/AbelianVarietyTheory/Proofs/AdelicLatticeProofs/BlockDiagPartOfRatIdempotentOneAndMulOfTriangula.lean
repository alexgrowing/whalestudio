import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem peirce_block_decomposition {A : Type*} [Ring A] (E F : A) (hE : E * E = E) (hF : F * F = F) (hEF : E * F = 0)
    (hFE : F * E = 0) (h1 : E + F = 1) :
    E * 1 * E + F * 1 * F = 1 ∧
    (∀ x y : A, F * x * E = 0 → F * y * E = 0 →
      E * (x * y) * E + F * (x * y) * F = (E * x * E + F * x * F) * (E * y * E + F * y * F) ∧
        F * (x * y) * E = 0) ∧
    (∀ x : A, F * x * E = 0 → x = (E * x * E + F * x * F) + E * x * F) ∧
    (∀ x : A, E * (E * x * E + F * x * F) * E + F * (E * x * E + F * x * F) * F = E * x * E + F * x * F) := by
  have hE' : ∀ z, E * (E * z) = E * z := fun z => by rw [← mul_assoc, hE]
  have hF' : ∀ z, F * (F * z) = F * z := fun z => by rw [← mul_assoc, hF]
  have hEF' : ∀ z, E * (F * z) = 0 := fun z => by rw [← mul_assoc, hEF, zero_mul]
  have hFE' : ∀ z, F * (E * z) = 0 := fun z => by rw [← mul_assoc, hFE, zero_mul]
  refine ⟨by rw [mul_one, mul_one, hE, hF, h1], ?_, ?_, ?_⟩
  · intro x y hx hy
    have hxy : x * y = x * (E + F) * y := by rw [h1, mul_one]
    have hx' : ∀ z, F * (x * (E * z)) = 0 := fun z => by
      rw [← mul_assoc, ← mul_assoc, hx, zero_mul]
    have hy' : F * (y * E) = 0 := by rw [← mul_assoc, hy]
    rw [hxy]
    constructor
    · simp only [mul_add, add_mul, mul_assoc, hE', hF', hEF', hFE', hx', hy', mul_zero, add_zero, zero_add]
    · simp only [mul_add, add_mul, mul_assoc, hx', hy', mul_zero, zero_mul, add_zero]
  · intro x hx
    calc x = (E + F) * x * (E + F) := by rw [h1, one_mul, mul_one]
      _ = E * x * E + F * x * F + E * x * F + F * x * E := by noncomm_ring
      _ = _ := by rw [hx, add_zero]
  · intro x
    simp only [mul_add, add_mul, mul_assoc, hE', hF', hEF', hFE', hE, hF, add_zero, zero_add]

theorem blk_mul_of_triangular : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (e : Matrix ι ι ℚ) (R : Type) [CommRing R] [Algebra ℚ R], e * e = e → blk e (1 : Matrix ι ι R) = 1 ∧ (∀ x y : Matrix ι ι R, (1 - e.map (algebraMap ℚ R)) * x * e.map (algebraMap ℚ R) = 0 → (1 - e.map (algebraMap ℚ R)) * y * e.map (algebraMap ℚ R) = 0 → blk e (x * y) = blk e x * blk e y ∧ (1 - e.map (algebraMap ℚ R)) * (x * y) * e.map (algebraMap ℚ R) = 0) ∧ (∀ x : Matrix ι ι R, (1 - e.map (algebraMap ℚ R)) * x * e.map (algebraMap ℚ R) = 0 → x = blk e x + e.map (algebraMap ℚ R) * x * (1 - e.map (algebraMap ℚ R))) ∧ (∀ x : Matrix ι ι R, blk e (blk e x) = blk e x) ∧ ∀ γ : Matrix ι ι ℚ, blk e (γ.map (algebraMap ℚ R)) = (blk e γ).map (algebraMap ℚ R) := by
  intro ι _ _ e R _ _ he
  have hE : e.map (algebraMap ℚ R) * e.map (algebraMap ℚ R) = e.map (algebraMap ℚ R) := by
    rw [← Matrix.map_mul, he]
  obtain ⟨h1, h2, h3, h4⟩ := peirce_block_decomposition (e.map (algebraMap ℚ R)) (1 - e.map (algebraMap ℚ R)) hE
    (by rw [sub_mul, mul_sub, mul_sub, hE]; simp) (by rw [mul_sub, hE]; simp)
    (by rw [sub_mul, hE]; simp) (by simp)
  refine ⟨h1, h2, h3, h4, ?_⟩
  intro γ
  have hid : e.map (algebraMap ℚ ℚ) = e := by
    ext i j
    simp
  change _ = (algebraMap ℚ R).mapMatrix (blk e γ)
  unfold blk
  rw [hid]
  simp only [map_add, map_mul, map_sub, map_one, RingHom.mapMatrix_apply]

end GlobalTheory.ClassFin
