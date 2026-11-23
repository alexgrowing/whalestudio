import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAffineOpenRingPolynomialEquiv
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DlogRatioVolumeFormNeZero
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standardAffineOpen_ring_polynomialEquiv : ∀ (k : Type) [Field k] (F : Type) [Field F] [Algebra k F] (d : ℕ) (x : Fin (d + 1) → F), IsPd k x → ∀ i : Fin (d + 1), ∃ e : MvPolynomial (Fin d) k ≃ₐ[k] rA k x {i}, ∀ j, (e (MvPolynomial.X j) : F) = x (i.succAbove j) / x i := by
  first | (exact @GlobalTheory.PD.rA_single_polyEquiv) | (exact GlobalTheory.PD.rA_single_polyEquiv) | (intros; apply GlobalTheory.PD.rA_single_polyEquiv <;> assumption)
