import Formalism.PeriodIntegrals.ExplicitFormulaCounts.ExplicitFormula
import Formalism.SharpRestriction.GlobalSchurBounds.ShortIntervalPrimes

namespace Formalism.MainNotions.ShortIntervalPrimes

theorem explicit_formula_bound_holds : ∃ C : ℝ, 0 < C ∧ ∀ D : Formalism.BasicNotions.D7, adm7 D C :=
  let ⟨C, hC, hh⟩ := explicitFormula_closed
  ⟨C, hC, fun _ => hh⟩

theorem family_explicit_formula_holds {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : adm7F Fm :=
  let ⟨C, hC, hh⟩ := explicit_formula_bound_holds
  ⟨C, hC, fun _ _ _ => hh _⟩

theorem zero_window_bound_holds : ∃ C : ℝ, 0 < C ∧ ∀ D : Formalism.BasicNotions.D7, adm11 D C :=
  let ⟨C, hC, hh⟩ := zerosWindow_closed
  ⟨C, hC, fun _ => hh⟩

theorem family_zero_window_holds {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : ComplementTwoFamily Fm :=
  let ⟨C, hC, hh⟩ := zero_window_bound_holds
  ⟨C, hC, fun _ _ _ => hh _⟩

end Formalism.MainNotions.ShortIntervalPrimes
