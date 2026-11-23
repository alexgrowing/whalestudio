import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CapelliCoeffDualWeylEqCoeffProd
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvalPol
open Formalism.CohomologicalDescent.DepthNonnegative GlobalTheory.ExpFrame Formalism.CohomologicalDescent.LD GlobalTheory.CapelliLink
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.capelliCoeff_dualWeyl_eq_coeff_prod : ∀ (O : Type) [CommRing O] [IsDomain O] [CharZero O] (N : ℕ), ∃ F : ℕ → FreeAlgebra O (Fin N × Fin N), ∀ ν : Fin N → ℕ, Antitone ν → ∀ f ∈ Formalism.GradedWeylDivisibility.dualWeyl O N N ν, ∀ k : ℕ, evalPol O N (F k) f = (((∏ a : Fin N, (Polynomial.X + Polynomial.C (((ν a : ℤ) - (a : ℕ) : ℤ)))).coeff k : ℤ) : O) • f := by
  first | exact @GlobalTheory.CapelliCoeffs.capelli_coeff_dualWeyl | exact GlobalTheory.CapelliCoeffs.capelli_coeff_dualWeyl | (intros; apply GlobalTheory.CapelliCoeffs.capelli_coeff_dualWeyl <;> assumption)
