import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueNormalizedCyclotomicTrace
import Development.AbelianVarietyTheory.Definitions.Foundations.ApplyEqOfMemAdjoin
import Development.AbelianVarietyTheory.Definitions.Foundations.IsTopWTopWOfExists
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unique_normalizedCyclotomicTrace : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (p : ℕ) [Fact p.Prime] (L m : ℕ), 1 ≤ m → m ≤ L → ∀ F : Ω, InZl ε p L F → ∃ F' : Ω, IsNT ε p L m F F' ∧ InZl ε p m F' ∧ ∀ F'' : Ω, IsNT ε p L m F F'' → F'' = F' := by
  first | exact @GlobalTheory.NTr.normTrace_exists_unique | exact GlobalTheory.NTr.normTrace_exists_unique | (intros; apply GlobalTheory.NTr.normTrace_exists_unique <;> assumption)
