import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzIntegralEqOfDerivs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzValuedIntegralLinear
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPairingStdP
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerInvariantFunctionalZero
open MeasureTheory

theorem UpperTheory.schrodinger_functional_eq_zero :
    ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (P : V → V → ℝ),
        GlobalTheory.ArchUniq.IsPairing P → ∀ g : SchwartzMap V ℂ, g ≠ 0 → ∀ l : SchwartzMap V ℂ →L[ℂ] ℂ,
        (∀ (w : V × V) (f : SchwartzMap V ℂ), ⇑f = GlobalTheory.ArchUniq.schrF P w ⇑g → l f = 0) → l = 0 := by
  intro V _ _ _ P hP g hg l hl
  exact GlobalTheory.SchrIrred.eq_zero_of_schrF P hP l g hg hl
