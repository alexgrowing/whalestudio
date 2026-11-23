import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeStableCongruenceConjDiamondMatrix
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.EigenOfTwoStep
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeLetterPreservesBasisSet
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.StabHecke
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeStableCongruence_conj_diamondMatrix : ∀ (N l d : ℕ) (σ : SL(2, ℤ)) (r : Matrix (Fin 2) (Fin 2) ℤ), IsDiam N l d σ → PP N l r → PP N l ((σ : Matrix (Fin 2) (Fin 2) ℤ) * r * ((σ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) := by
  first | exact @GlobalTheory.KZ.StabHecke.congruenceCondition_conj_diamond | exact GlobalTheory.KZ.StabHecke.congruenceCondition_conj_diamond | (intros; apply GlobalTheory.KZ.StabHecke.congruenceCondition_conj_diamond <;> assumption)
