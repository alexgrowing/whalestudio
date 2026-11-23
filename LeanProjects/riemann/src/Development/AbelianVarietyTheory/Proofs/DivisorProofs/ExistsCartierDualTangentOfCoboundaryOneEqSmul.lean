import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

noncomputable section

namespace GlobalTheory

namespace PDiv

open Coalgebra Bialgebra

theorem exists_tangent_of_cobOne_eq_smul (O A : Type) [CommRing O] [CommRing A] [Bialgebra O A]
    [Module.Finite O A] [Module.Projective O A] [Coalgebra.IsCocomm O A] (a : O) (b : A)
    (z : A ⊗[O] A) (h : cobOne O A b = a • z) :
    ∃ u : Cot O (CartierDual O A) →ₗ[O] O ⧸ Ideal.span {a},
      ∀ φ : CartierDual O A, u (dUnit O φ) = Ideal.Quotient.mk _ (φ b) := by
  let D : CartierDual O A →ₗ[O] O ⧸ Ideal.span {a} :=
    (Ideal.Quotient.mkₐ O (Ideal.span {a})).toLinearMap ∘ₗ CartierDual.evalAt O A b
  have hcomul : comul b = b ⊗ₜ 1 + 1 ⊗ₜ b + a • z := by
    rw [← h, cobOne_apply]; abel
  have hD : ∀ φ ψ : CartierDual O A, D (φ * ψ) =
      counitAlgHom O (CartierDual O A) φ • D ψ + counitAlgHom O (CartierDual O A) ψ • D φ := by
    intro φ ψ
    have e : (φ * ψ) b = φ b * ψ 1 + φ 1 * ψ b + a * CartierDual.pair O A A (φ ⊗ₜ ψ) z := by
      rw [CartierDual.mul_apply, hcomul, map_add, map_add, map_smul]
      simp
    have ha : Ideal.Quotient.mk (Ideal.span {a}) a = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span rfl)
    simp only [D, LinearMap.comp_apply, CartierDual.evalAt_apply, AlgHom.toLinearMap_apply,
      Ideal.Quotient.mkₐ_eq_mk, e, map_add, map_mul, ha, zero_mul, add_zero, Algebra.smul_def,
      Ideal.Quotient.algebraMap_eq]
    rw [show counitAlgHom O (CartierDual O A) φ = φ 1 from rfl,
      show counitAlgHom O (CartierDual O A) ψ = ψ 1 from rfl]
    ring
  exact ⟨AugCot.lift _ D hD, fun φ => AugCot.lift_d _ D hD φ⟩

end PDiv

end GlobalTheory
