import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodRing
open Matrix

namespace GlobalTheory

theorem detfix_unitary_transvection {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n]
    (τ : R →+* R) (H : Matrix n n R) (e : n → R) (p u s : R) (k : ℕ)
    (hτ : ∀ a, τ (τ a) = a) (hH : Formalism.UG.cT τ H = H) (ha : IsUnit (Formalism.UG.hform τ H e e))
    (hu : u * τ u = 1) (hu1 : u = 1 + p ^ (k + 1) * s) :
    ∃ g M : Matrix n n R, Formalism.UG.cT τ g * H * g = H ∧ g.det = u ∧ g = 1 + p ^ (k + 1) • M := by
  have hHij : ∀ i j, τ (H j i) = H i j := fun i j => by
    have := congrFun (congrFun hH i) j
    simpa [Formalism.UG.cT] using this
  set a := Formalism.UG.hform τ H e e with ha_def
  obtain ⟨b, hab⟩ : ∃ b, a * b = 1 := ⟨ha.unit⁻¹.1, ha.mul_val_inv⟩
  have hτa : τ a = a := by
    simp only [ha_def, Formalism.UG.hform, map_sum, map_mul, hτ, hHij]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hτb : τ b = b := by
    have h1 : a * τ b = 1 := by rw [← hτa, ← map_mul, hab, map_one]
    calc τ b = (b * a) * τ b := by rw [mul_comm b a, hab, one_mul]
      _ = b := by rw [mul_assoc, h1, mul_one]
  set r : n → R := fun j => ∑ i, τ (e i) * H i j with hr
  have hre : r ⬝ᵥ e = a := by
    simp only [dotProduct, hr, ha_def, Formalism.UG.hform, Finset.sum_mul]
    rw [Finset.sum_comm]
  have hτr : ∀ i, τ (r i) = ∑ l, H i l * e l := fun i => by
    simp only [hr, map_sum, map_mul, hτ, hHij]
    refine Finset.sum_congr rfl fun l _ => ?_
    ring
  set X : Matrix n n R := vecMulVec e r with hX
  have hXH : Formalism.UG.cT τ X * H = H * X := by
    ext i j
    simp only [Formalism.UG.cT, mul_apply, transpose_apply, map_apply, hX, vecMulVec_apply, map_mul]
    rw [hτr i]
    simp only [hr, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ => ?_
    ring
  have hXX : X * X = a • X := by
    rw [hX, vecMulVec_mul_vecMulVec, hre]
    ext i j; simp [vecMulVec_apply]; ring
  set c := (u - 1) * b with hc
  have hcT : Formalism.UG.cT τ (1 + c • X) = 1 + τ c • Formalism.UG.cT τ X := by
    ext i j
    simp [Formalism.UG.cT, one_apply, eq_comm]
  have hkey : c + τ c + τ c * c * a = 0 := by
    have hτu : τ u - 1 = τ (u - 1) := by simp
    rw [hc, map_mul, hτb]
    have : (u - 1) * b + (τ u - 1) * b + (τ u - 1) * b * ((u - 1) * b) * a
        = b * (u * τ u - 1) + (τ u - 1) * (u - 1) * b * (a * b - 1) := by ring
    rw [map_sub, map_one, this, hu, hab]; ring
  refine ⟨1 + c • X, (s * b) • X, ?_, ?_, ?_⟩
  · rw [hcT]
    have : (1 + τ c • Formalism.UG.cT τ X) * H * (1 + c • X)
        = H + (c + τ c + τ c * c * a) • (H * X) := by
      simp only [add_mul, mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul,
        hXH, smul_smul, add_smul]
      rw [Matrix.mul_assoc H X X, hXX, Matrix.mul_smul, smul_smul]
      rw [mul_comm c (τ c)]; abel
    rw [this, hkey, zero_smul, add_zero]
  · rw [hX, ← vecMulVec_smul, vecMulVec_eq Unit, det_one_add_replicateCol_mul_replicateRow,
      smul_dotProduct, hre, smul_eq_mul, hc]
    calc 1 + (u - 1) * b * a = 1 + (u - 1) * (a * b) := by ring
      _ = u := by rw [hab]; ring
  · rw [smul_smul, hc, hu1]; congr 2; ring

end GlobalTheory
