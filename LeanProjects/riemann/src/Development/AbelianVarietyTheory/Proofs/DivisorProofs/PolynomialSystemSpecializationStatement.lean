import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialSystemSpecialization
import Mathlib
open Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polynomial_system_specialization : ∀ (k C : Type) [Field k] [CharZero k] [Field C] [Algebra k C] (m : ℕ) (a : Fin m → C), ∃ (d : ℕ) (t : Fin d → C) (θ : C) (P : Polynomial (MvPolynomial (Fin d) k)) (Δ : MvPolynomial (Fin d) k) (Q : Fin m → Polynomial (MvPolynomial (Fin d) k)), P.Monic ∧ Polynomial.eval₂ (MvPolynomial.aeval t).toRingHom θ P = 0 ∧ MvPolynomial.aeval t Δ ≠ 0 ∧ (∀ j, Polynomial.eval₂ (MvPolynomial.aeval t).toRingHom θ (Q j) = MvPolynomial.aeval t Δ * a j) ∧ ∀ (B : Type) [Field B] [Algebra k B] (t' : Fin d → B) (θ' : B), MvPolynomial.aeval t' Δ ≠ 0 → Polynomial.eval₂ (MvPolynomial.aeval t').toRingHom θ' P = 0 → ∃ f : Algebra.adjoin k (Set.range a) →ₐ[k] B, ∀ j, Polynomial.eval₂ (MvPolynomial.aeval t').toRingHom θ' (Q j) = MvPolynomial.aeval t' Δ * f ⟨a j, Algebra.subset_adjoin (Set.mem_range_self j)⟩ := by
  first | exact @GlobalTheory.fg_field_structure_specialisation | exact GlobalTheory.fg_field_structure_specialisation | (intros; apply GlobalTheory.fg_field_structure_specialisation <;> assumption)
