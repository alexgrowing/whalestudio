import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralUnitsFiniteCosets
import Mathlib
import Formalism.LocalToGlobal.Divisibility.Tuples
open NumberField IsDedekindDomain Formalism.L2.DIV Formalism.UG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_units_finite_cosets : ∀ (L : Type) [Field L] [NumberField L] (N : ℕ), 0 < N →
    ∃ S : Finset (AfE ℚ L)ˣ, ∀ k ∈ intU ℚ L, ∃ s ∈ S, s⁻¹ * k ∈ congN ℚ L N := by
  first | exact @GlobalTheory.congN_finite_index | exact GlobalTheory.congN_finite_index | (intros; apply GlobalTheory.congN_finite_index <;> assumption)
