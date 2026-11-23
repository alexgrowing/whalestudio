import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularTowerMemAdjoinJOfSlTwoIntInvariant
import Development.AbelianVarietyTheory.Definitions.Foundations.ApplyEqOfMemAdjoin
import Development.AbelianVarietyTheory.Definitions.Foundations.IsTopWTopWOfExists
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.modularTower_mem_adjoin_j_of_slTwoInt_invariant : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : GlobalTheory.KZ.Tower Ω ε), (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ f : X.K, (∀ γ : SL(2, ℤ), X.sl (ofSL γ) f = f) → f ∈ IntermediateField.adjoin Ω {X.jK} := by
  first | exact @GlobalTheory.KZ.LevelOneFrac.mem_adjoin_of_sl_inv | exact GlobalTheory.KZ.LevelOneFrac.mem_adjoin_of_sl_inv | (intros; apply GlobalTheory.KZ.LevelOneFrac.mem_adjoin_of_sl_inv <;> assumption)
