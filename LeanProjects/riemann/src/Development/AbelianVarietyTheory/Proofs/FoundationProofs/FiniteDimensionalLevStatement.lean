import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteDimensionalLev
import Development.AbelianVarietyTheory.Definitions.Foundations.HahnPowOrderLeadingCoeff
open scoped MatrixGroups
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteDimensional_lev_of_gamma_le : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : GlobalTheory.KZ.Tower Ω ε) (Γ' : Subgroup SL(2, ℤ)) (M : ℕ), 0 < M → CongruenceSubgroup.Gamma M ≤ Γ' → letI := GlobalTheory.K4.algRat X Γ'; FiniteDimensional (RatFunc Ω) (GlobalTheory.K4.lev X Γ') := by
  first | exact @GlobalTheory.K4.finiteDimensional_lev | exact GlobalTheory.K4.finiteDimensional_lev | (intros; apply GlobalTheory.K4.finiteDimensional_lev <;> assumption)
