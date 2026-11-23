import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizationSymmetricFormIdentity
import Mathlib
open MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarization_symmetric_form_identity : ∀ {V J : Type} [AddCommGroup V] [Module ℝ V] (e : ℕ) (Ψ : MvPolynomial J ℝ →ₗ[ℝ] ℝ) (x ℓ : MvPolynomial J ℝ) (num : MultilinearMap ℝ (fun _ : Fin (e + 1) => V) ℝ), (∀ (v : Fin (e + 1) → V) (ρ : Equiv.Perm (Fin (e + 1))), num (v ∘ ρ) = num v) → ∀ (ν : ℝ) (w a : V), (∀ t : ℤ, Ψ ((MvPolynomial.C (t : ℝ) * x + ℓ) ^ (e + 1)) = ν * num (fun _ => w + (t : ℝ) • a)) → Ψ (x * ℓ ^ e) = ν * num (Fin.cons a fun _ => w) := by
  first | exact @GlobalTheory.linear_coeff_compare | exact GlobalTheory.linear_coeff_compare | (intros; apply GlobalTheory.linear_coeff_compare <;> assumption)
