import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SubstUpperTriangularHahnMulAndOne
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsRootOfIsAlgClosed
open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.substUpperTriangularHahn_mul_and_one : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] (ε : Ω →+* ℂ) (a b d : ℚ), 0 < a / d → ∀ φ ψ : HahnSeries ℚ Ω,
  sub ε a b d (φ * ψ) = sub ε a b d φ * sub ε a b d ψ ∧ sub ε a b d 1 = 1 := by
  first | exact @GlobalTheory.CyclotomicQExpansion.sub_mul_and_one | exact GlobalTheory.CyclotomicQExpansion.sub_mul_and_one | (intros; apply GlobalTheory.CyclotomicQExpansion.sub_mul_and_one <;> assumption)
