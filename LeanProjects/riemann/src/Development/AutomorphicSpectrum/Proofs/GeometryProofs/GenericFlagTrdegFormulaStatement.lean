import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericFlagTrdegFormula
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsGenericFlag
open GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_flag_trdeg_formula : ∀ (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] [Algebra Ω₀ Ω] (E : Type) [AddCommGroup E] [Module Ω₀ E] (E' : Type) [AddCommGroup E'] [Module Ω E'] (j : E →+ E') (S : Type) [Fintype S] (r : S → ℕ) (V : S → Submodule Ω₀ E) (b₀ : ∀ σ, Fin (r σ) → E') (d : ℕ), IsGenericFlag (Ω' := Ω) j V b₀ d → Algebra.trdeg Ω₀ Ω = ((∑ σ, r σ * (r σ - 1) / 2 : ℕ) : Cardinal) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagTrdeg.trdeg_of_isGenericFlag | exact GlobalTheory.CompanionTheory.Ar.FlagTrdeg.trdeg_of_isGenericFlag | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagTrdeg.trdeg_of_isGenericFlag <;> assumption)
