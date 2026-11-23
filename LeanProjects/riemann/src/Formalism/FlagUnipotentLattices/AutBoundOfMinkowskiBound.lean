import Formalism.FlagUnipotentLattices.MemOfOrthogonalAnisotropic
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.ExistsHasLeadingCoeffOfMemSpanBelow
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.MinkowskiNumberDvdFactorial

namespace Formalism.HermitianLatticeCounting.Final.S6

theorem y1 : Formalism.HermitianLatticeCounting.S6.Y1 := by
  first
    | exact Formalism.HermitianLatticeCounting.P.wedgeMapInLieAlgebra
    | exact Formalism.HermitianLatticeCounting.P.S6e.wedgeMapInLieAlgebra
theorem n0c : Formalism.HermitianLatticeCounting.S6.MemOfOrthogonalAnisotropic := by
  first
    | exact Formalism.HermitianLatticeCounting.P.memOfOrthogonalAnisotropic
    | exact Formalism.HermitianLatticeCounting.P.S6e.memOfOrthogonalAnisotropic
theorem nFJZero : Formalism.HermitianLatticeCounting.S6.NFJZero := by
  first
    | exact Formalism.HermitianLatticeCounting.P.normalFormZero
    | exact Formalism.HermitianLatticeCounting.P.S6e.normalFormZero

theorem normalForm : Formalism.HermitianLatticeCounting.S6.NormalForm := by
  first
    | exact Formalism.HermitianLatticeCounting.P.existsNormalForm
    | exact Formalism.HermitianLatticeCounting.P.S6e.existsNormalForm

theorem normSgBound : Formalism.HermitianLatticeCounting.S6.NormSgBound := by
  first
    | exact Formalism.HermitianLatticeCounting.P.norm_singular_value_bound
    | exact Formalism.HermitianLatticeCounting.P.S6e.norm_singular_value_bound

theorem minkowskiDvdFactorial : Formalism.HermitianLatticeCounting.S6.MinkowskiDvdFactorial := by
  first
    | exact Formalism.HermitianLatticeCounting.P.minkowski_number_dvd_factorial
    | exact Formalism.HermitianLatticeCounting.P.S6e.minkowski_number_dvd_factorial
theorem autBound_of_minkowskiBound : Formalism.HermitianLatticeCounting.S6.MinkowskiBound → Formalism.HermitianLatticeCounting.S6.AutBound := by
  intro hMk s f G hG
  have h1 := (hMk (2 * s * f) G hG).trans (minkowskiDvdFactorial (2 * s * f))
  have h2 : Nat.card G ≤ (2 * (2 * s * f)).factorial := Nat.le_of_dvd (Nat.factorial_pos _) h1
  have h3 : (2 * (2 * s * f)).factorial ≤ (4 * s * f) ^ (4 * s * f) := by
    have e : 2 * (2 * s * f) = 4 * s * f := by ring
    rw [e]
    exact Nat.factorial_le_pow _
  exact_mod_cast h2.trans h3

theorem expIdentity : Formalism.HermitianLatticeCounting.S6.ExpIdentity := by
  first
    | exact Formalism.HermitianLatticeCounting.P.exponential_identity
    | exact Formalism.HermitianLatticeCounting.P.S6e.exponential_identity
theorem finalSum : Formalism.HermitianLatticeCounting.S6.FinalSum := by
  first
    | exact Formalism.HermitianLatticeCounting.P.final_sum_bound
    | exact Formalism.HermitianLatticeCounting.P.S6e.final_sum_bound

end Formalism.HermitianLatticeCounting.Final.S6
