import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranscendenceBasisAlgebraicStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveElementFiniteAlgebraicStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MonicPolynomialPrimitiveOverBasisStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveElementCoordinatePolynomialsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveElementDenominatorClearingStatement
open Polynomial

namespace GlobalTheory

theorem fg_field_structure_specialisation : ∀ (k C : Type) [Field k] [CharZero k] [Field C] [Algebra k C] (m : ℕ) (a : Fin m → C), ∃ (d : ℕ) (t : Fin d → C) (θ : C) (P : Polynomial (MvPolynomial (Fin d) k)) (Δ : MvPolynomial (Fin d) k) (Q : Fin m → Polynomial (MvPolynomial (Fin d) k)), P.Monic ∧ Polynomial.eval₂ (MvPolynomial.aeval t).toRingHom θ P = 0 ∧ MvPolynomial.aeval t Δ ≠ 0 ∧ (∀ j, Polynomial.eval₂ (MvPolynomial.aeval t).toRingHom θ (Q j) = MvPolynomial.aeval t Δ * a j) ∧ ∀ (B : Type) [Field B] [Algebra k B] (t' : Fin d → B) (θ' : B), MvPolynomial.aeval t' Δ ≠ 0 → Polynomial.eval₂ (MvPolynomial.aeval t').toRingHom θ' P = 0 → ∃ f : Algebra.adjoin k (Set.range a) →ₐ[k] B, ∀ j, Polynomial.eval₂ (MvPolynomial.aeval t').toRingHom θ' (Q j) = MvPolynomial.aeval t' Δ * f ⟨a j, Algebra.subset_adjoin (Set.mem_range_self j)⟩ := by
  intro k C _ _ _ _ m a
  obtain ⟨d, t, ht, halg⟩ := GlobalTheory.T.exists_transcendence_basis_algebraic k C m a
  haveI : CharZero C := charZero_of_injective_algebraMap (algebraMap k C).injective
  obtain ⟨α, hα, hαa⟩ := GlobalTheory.T.primitive_element_finite_algebraic (IntermediateField.adjoin k (Set.range t)) C m a halg
  obtain ⟨θ, P, hPm, hP0, hθ, hαθ, hdvd⟩ := GlobalTheory.T.monic_polynomial_primitive_over_basis k C d t α ht hα
  have hx : ∀ j, a j ∈ IntermediateField.adjoin (IntermediateField.adjoin k (Set.range t)) {θ} := by
    intro j
    exact (IntermediateField.adjoin_simple_le_iff.mpr hαθ) (hαa j)
  obtain ⟨Δ, Q, hΔ, hQ⟩ := GlobalTheory.T.primitive_element_coordinate_polynomials k C d m t θ a hθ hx
  exact ⟨d, t, θ, P, Δ, Q, hPm, hP0, hΔ, hQ, fun B _ _ t' θ' h1 h2 =>
    GlobalTheory.T.primitive_element_denominator_clearing k C m d a t θ P Δ Q hΔ hQ hdvd B t' θ' h1 h2⟩

end GlobalTheory
