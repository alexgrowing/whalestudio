import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteUnitsModSquaresOfUnramifiedQuadratic
import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
open GlobalTheory.UnitLemma
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_units_mod_squares_of_unramifiedQuadratic : ∀ (K : UQ) (L : Type) [Field L] [Algebra K.E L] [FiniteDimensional K.E L], Finite (Lˣ ⧸ (powMonoidHom 2 : Lˣ →* Lˣ).range) := by
  first | exact @GlobalTheory.UnitLemma.UQ.finite_units_mod_sq | exact GlobalTheory.UnitLemma.UQ.finite_units_mod_sq | (intros; apply GlobalTheory.UnitLemma.UQ.finite_units_mod_sq <;> assumption)
