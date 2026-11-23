import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SesquilinearEqZeroOfDiagZero
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sesquilinear_eq_zero_of_diag_zero : ∀ {V : Type} [AddCommGroup V] [Module ℂ V] (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ), (∀ v, B v v = 0) → B = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Sesquilinear.eq_zero_of_diag_eq_zero | exact GlobalTheory.CompanionTheory.Sesquilinear.eq_zero_of_diag_eq_zero | (intros; apply GlobalTheory.CompanionTheory.Sesquilinear.eq_zero_of_diag_eq_zero <;> assumption)
