import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SameBlockOfPosC

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible

namespace GlobalTheory.FockTensor

theorem derived_adjoint_and_casimir (p q : ℕ) (T : GrpData p q) (πU : URep T) (V₁ V₂ : Type)
    [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂]
    (a₁ : Mat p q →ₗ[ℂ] Module.End ℂ V₁) (a₂ : Mat p q →ₗ[ℂ] Module.End ℂ V₂)
    (E₁ : V₁ →ₗ[ℂ] πU.H) (E₂ : V₂ →ₗ[ℂ] πU.H)
    (h₁ : ∀ Y ∈ upq p q, ∀ x,
      HasDerivAt (fun t : ℝ => πU.π (T.expt (t • Y)) (E₁ x)) (E₁ (a₁ Y x)) 0)
    (h₂ : ∀ Y ∈ upq p q, ∀ y,
      HasDerivAt (fun t : ℝ => πU.π (T.expt (t • Y)) (E₂ y)) (E₂ (a₂ Y y)) 0) :
    (∀ Z x y, inner ℂ (E₁ (a₁ Z x)) (E₂ y) = inner ℂ (E₁ x) (E₂ (a₂ (adjZ Z) y))) ∧
      ∀ x y, inner ℂ (E₁ (casimir a₁ x)) (E₂ y) = inner ℂ (E₁ x) (E₂ (casimir a₂ y)) := by
  have hreal : ∀ Y ∈ upq p q, ∀ x y,
      inner ℂ (E₁ (a₁ Y x)) (E₂ y) = - inner ℂ (E₁ x) (E₂ (a₂ Y y)) := by
    intro Y hY x y
    have h := (h₁ Y hY x).inner ℂ (h₂ Y hY y)
    simp only [inner_pi_pi] at h
    have h0 := h.unique (hasDerivAt_const (0 : ℝ) _)
    simp only [zero_smul, T.expt_zero, map_one, ContinuousLinearMap.one_apply] at h0
    linear_combination h0
  have hZ : ∀ Z x y, inner ℂ (E₁ (a₁ Z x)) (E₂ y) = inner ℂ (E₁ x) (E₂ (a₂ (adjZ Z) y)) := by
    intro Z x y
    obtain ⟨X, hX, Y, hY, rfl⟩ := exists_upq_add Z
    rw [adjZ_add, adjZ_smul, (mem_upq_iff X).1 hX, (mem_upq_iff Y).1 hY]
    simp only [map_add, map_smul, map_neg, LinearMap.add_apply, LinearMap.smul_apply,
      LinearMap.neg_apply, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
      inner_neg_right, hreal X hX, hreal Y hY]
    rfl
  refine ⟨hZ, fun x y => ?_⟩
  simp only [casimir, LinearMap.sum_apply, map_sum, sum_inner, inner_sum, Module.End.mul_apply]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [hZ, hZ, adjZ_Eab, adjZ_Eab]
  simp only [map_smul, LinearMap.smul_apply, inner_smul_right]
  linear_combination (sgnIx b * sgnIx b * inner ℂ (E₁ x) (E₂ (a₂ (Eab a b) (a₂ (Eab b a) y)))) *
    sgnIx_mul_self a + inner ℂ (E₁ x) (E₂ (a₂ (Eab a b) (a₂ (Eab b a) y))) * sgnIx_mul_self b

end GlobalTheory.FockTensor
