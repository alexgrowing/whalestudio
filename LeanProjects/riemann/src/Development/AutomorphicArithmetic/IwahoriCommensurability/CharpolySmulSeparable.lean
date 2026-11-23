import Mathlib
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CharpolySmul

open Polynomial

namespace UpperTheory

theorem charpoly_smul_alt {k ι : Type*} [Field k] [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι k) {c : k} (hc : c ≠ 0) :
    (c • M).charpoly =
      C (c ^ Fintype.card ι) * M.charpoly.comp (C c⁻¹ * X) :=
  _root_.UpperTheory.Reformulated.B.Qh50.charpoly_smul_alt M hc

theorem charpoly_smul_separable :
    ∀ (k : Type) [Field k] (n : ℕ) (c : k), c ≠ 0 → ∀ M : Matrix (Fin n) (Fin n) k, M.charpoly.Separable → (c • M).charpoly.Separable := by
  intro k _ n c hc M h
  have hcc : (C c : k[X]) * C c⁻¹ = 1 := by rw [← C_mul, mul_inv_cancel₀ hc, C_1]
  rw [charpoly_smul_alt M hc]
  have hcomp : (M.charpoly.comp (C c⁻¹ * X)).Separable := by
    obtain ⟨a, b, hab⟩ := h
    refine ⟨a.comp (C c⁻¹ * X), b.comp (C c⁻¹ * X) * C c, ?_⟩
    have h1 := congrArg (fun p : k[X] => p.comp (C c⁻¹ * X)) hab
    simp only [add_comp, mul_comp, one_comp] at h1
    rw [derivative_comp, ← h1]
    simp only [derivative_mul, derivative_C, derivative_X, zero_mul, zero_add, mul_one]
    linear_combination ((b.comp (C c⁻¹ * X)) * (derivative M.charpoly).comp (C c⁻¹ * X)) * hcc
  have hu : IsUnit (C (c ^ Fintype.card (Fin n)) : k[X]) :=
    isUnit_C.2 (pow_ne_zero _ hc).isUnit
  rw [Polynomial.Separable, derivative_mul, derivative_C, zero_mul, zero_add]
  exact (isCoprime_mul_unit_left hu _ _).2 hcomp

end UpperTheory
