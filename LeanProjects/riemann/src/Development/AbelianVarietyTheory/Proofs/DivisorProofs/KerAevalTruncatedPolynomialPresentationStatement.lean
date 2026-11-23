import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerAevalTruncatedPolynomialPresentation
import Mathlib
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ker_aeval_truncatedPolynomial_presentation : ∀ (n : ℕ), 0 < n → ∀ (B A : Type) [CommRing B] [CommRing A] [Algebra B A] (d : ℕ) (x : Fin d → A) (b : Fin d → B), (∀ i, x i ^ n = algebraMap B A (b i)) → LinearIndependent B (fun a : Fin d → Fin n => ∏ i, x i ^ (a i : ℕ)) → RingHom.ker (MvPolynomial.aeval x : MvPolynomial (Fin d) B →ₐ[B] A) = Ideal.span (Set.range fun i : Fin d => (MvPolynomial.X i ^ n - MvPolynomial.C (b i) : MvPolynomial (Fin d) B)) := by
  first | exact @GlobalTheory.ker_aeval_truncated | exact GlobalTheory.ker_aeval_truncated | (intros; apply GlobalTheory.ker_aeval_truncated <;> assumption)
