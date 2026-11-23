import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InverseDoubleCosetNonsplit
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inverse_double_coset_nonsplit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (n : ℕ) (g : UL n w), ∃ k₁ ∈ KL n w, ∃ k₂ ∈ KL n w, g⁻¹ = k₁ * g * k₂ := by
  first | exact @GlobalTheory.CompanionTheory.InvDoubleCoset.inv_mem_doubleCoset | exact GlobalTheory.CompanionTheory.InvDoubleCoset.inv_mem_doubleCoset | (intros; apply GlobalTheory.CompanionTheory.InvDoubleCoset.inv_mem_doubleCoset <;> assumption)
