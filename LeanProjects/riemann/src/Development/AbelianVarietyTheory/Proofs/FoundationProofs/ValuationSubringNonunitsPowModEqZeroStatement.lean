import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationSubringNonunitsPowModEqZero
import Development.AbelianVarietyTheory.Definitions.Foundations.ApplyEqOfMemAdjoin
import Development.AbelianVarietyTheory.Definitions.Foundations.IsTopWTopWOfExists
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuationSubring_nonunits_pow_modEq_zero : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω), ((l : ℕ) : Ω) ∈ A.nonunits → ∀ x ∈ A.nonunits, ∃ k : ℕ, CgA A l 1 (x ^ k) 0 := by
  first | exact @GlobalTheory.cgA_pow_of_mem_nonunits | exact GlobalTheory.cgA_pow_of_mem_nonunits | (intros; apply GlobalTheory.cgA_pow_of_mem_nonunits <;> assumption)
