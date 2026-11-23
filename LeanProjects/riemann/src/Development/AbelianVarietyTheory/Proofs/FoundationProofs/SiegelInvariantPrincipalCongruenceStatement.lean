import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SiegelInvariantPrincipalCongruence
import Development.AbelianVarietyTheory.Definitions.Foundations.SgC
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
open scoped UpperHalfPlane MatrixGroups
open GlobalTheory.KZ GlobalTheory.Sieg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegel_invariant_principal_congruence : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Tower Ω ε) (c : ℕ) (x : Fin 2 → ℚ) (M : ℕ), admitted c x → 0 < M → (∃ a b : ℤ, x 0 = a / M ∧ x 1 = b / M) → ∀ γ ∈ CongruenceSubgroup.Gamma M, T.sl (ofSL γ) (siegel T c x) = siegel T c x := by
  first | exact @GlobalTheory.KZ.siegel_level | exact GlobalTheory.KZ.siegel_level | (intros; apply GlobalTheory.KZ.siegel_level <;> assumption)
