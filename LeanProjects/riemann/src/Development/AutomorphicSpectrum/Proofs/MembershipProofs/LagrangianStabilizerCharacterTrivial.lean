import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.ExistsEqMulApplyZero
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.SplitQuadraticAlgebraOrder
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.ExistsInvariantForm

open Matrix ValuativeRel GlobalTheory.WeilM MeasureTheory
open scoped ComplexConjugate NNReal

namespace GlobalTheory.CompanionTheory.SplitUnique

section Alg

variable {R : Type} [CommRing R] {E : Type} [CommRing E] [Algebra R E] (c : E →ₐ[R] E)
  {α β : Type} [Fintype α] [Fintype β]

theorem hTens_eq (JA : Matrix α α E) (JB : Matrix β β E) (x y : Matrix α β E) :
    hTens c JA JB x y = ∑ i, ∑ k, JA i k * (x * JB * (y.map c)ᵀ) i k := by
  unfold hTens
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hTens_eq_zero (JA : Matrix α α E) {JB : Matrix β β E} {ν : Type} [Fintype ν] {Cy : Matrix β ν E}
    (h : Cyᵀ * JB * Cy.map c = 0) (z z' : Matrix α ν E) : hTens c JA JB (z * Cyᵀ) (z' * Cyᵀ) = 0 := by
  rw [hTens_eq]
  have hm : z * Cyᵀ * JB * ((z' * Cyᵀ).map c)ᵀ = 0 := by
    have hmap : (z' * Cyᵀ).map c = z'.map c * (Cyᵀ).map c := by
      simp
    rw [hmap, Matrix.transpose_mul, Matrix.transpose_map, Matrix.transpose_transpose,
      show z * Cyᵀ * JB * (Cy.map c * (z'.map c)ᵀ) = z * (Cyᵀ * JB * Cy.map c) * (z'.map c)ᵀ by
        simp only [Matrix.mul_assoc], h]
    simp
  rw [hm]
  simp

variable [DecidableEq β]

end Alg

end GlobalTheory.CompanionTheory.SplitUnique
