import Mathlib
import Formalism.PeriodIntegrals.ScMuExists
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MeasureDecomposition.InstDecomp

noncomputable section

open Matrix

namespace PI.ScMuExists.UnitaryGroupMassFormula

variable (I : Formalism.MainNotions.S.AutInst)

theorem phi_star (v : NumberField.InfinitePlace I.F) (a : I.E) : I.φ v (star a) = star (I.φ v a) :=
  I.cm.cmUnram.2.1 (I.φ v) a

theorem gram_real (v : NumberField.InfinitePlace I.F) :
    ((I.P v)⁻¹)ᴴ * Formalism.REAL.Jm (I.ε v) * (I.P v)⁻¹ = I.J.map (I.φ v) := by
  have h : I.P v * (I.P v)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp (I.P_unit v))
  have e : ((I.P v)⁻¹)ᴴ * (I.P v)ᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, h, Matrix.conjTranspose_one]
  rw [← I.P_spec v]
  calc ((I.P v)⁻¹)ᴴ * ((I.P v)ᴴ * I.J.map (I.φ v) * I.P v) * (I.P v)⁻¹
      = (((I.P v)⁻¹)ᴴ * (I.P v)ᴴ) * I.J.map (I.φ v) * (I.P v * (I.P v)⁻¹) := by
        simp only [Matrix.mul_assoc]
    _ = I.J.map (I.φ v) := by rw [e, h, Matrix.one_mul, Matrix.mul_one]

theorem hJ_mulVec_gen {n : ℕ} (ε : Fin n → Bool) (A : Matrix (Fin n) (Fin n) ℂ) (u w : Fin n → ℂ) :
    hJ ε (A *ᵥ u) (A *ᵥ w) = star u ⬝ᵥ ((Aᴴ * Formalism.REAL.Jm ε * A) *ᵥ w) := by
  simp only [hJ, Matrix.star_mulVec, Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    Matrix.vecMul_vecMul, Matrix.mul_assoc]

theorem rv_hJ (v : NumberField.InfinitePlace I.F) (x y : Fin I.n → I.E) :
    hJ (I.ε v) (rv I v x) (rv I v y) = I.φ v (Formalism.UG.hform (starRingEnd I.E) I.J x y) := by
  simp only [rv]
  rw [hJ_mulVec_gen, gram_real I v]
  simp only [Formalism.UG.hform, map_sum, map_mul, dotProduct, Matrix.mulVec, Pi.star_apply,
    Matrix.map_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [starRingEnd_apply, phi_star I v]
  ring

theorem hJ_conj {n : ℕ} (ε : Fin n → Bool) (u w : Fin n → ℂ) : hJ ε w u = star (hJ ε u w) := by
  simp only [hJ, Formalism.REAL.Jm, dotProduct, Matrix.mulVec_diagonal, star_sum, star_mul',
    Pi.star_apply, star_star]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : ε i = true <;> simp [h] <;> ring

variable {I}

theorem rv_frame {r : ℕ} {e f : Fin r → Fin I.n → I.E} {z : Fin I.n → I.E} (hF : IsFrame I e f z)
    (v : NumberField.InfinitePlace I.F) :
    (∀ a b, hJ (I.ε v) (rv I v (e a)) (rv I v (e b)) = 0) ∧
    (∀ a b, hJ (I.ε v) (rv I v (f a)) (rv I v (f b)) = 0) ∧
    (∀ a b, hJ (I.ε v) (rv I v (e a)) (rv I v (f b)) = if a = b then 1 else 0) ∧
    (∀ a, hJ (I.ε v) (rv I v (e a)) (rv I v z) = 0 ∧ hJ (I.ε v) (rv I v (f a)) (rv I v z) = 0) ∧
    hJ (I.ε v) (rv I v z) (rv I v z) ≠ 0 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hF
  refine ⟨fun a b => ?_, fun a b => ?_, fun a b => ?_, fun a => ?_, ?_⟩
  · rw [rv_hJ, h1, map_zero]
  · rw [rv_hJ, h2, map_zero]
  · rw [rv_hJ, h3]
    split_ifs <;> simp
  · rw [rv_hJ, rv_hJ, (h4 a).1, (h4 a).2, map_zero]
    exact ⟨rfl, rfl⟩
  · rw [rv_hJ]
    exact (map_ne_zero _).mpr h5

end PI.ScMuExists.UnitaryGroupMassFormula
