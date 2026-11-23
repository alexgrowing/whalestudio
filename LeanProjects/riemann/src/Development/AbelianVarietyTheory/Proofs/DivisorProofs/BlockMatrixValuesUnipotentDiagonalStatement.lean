import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockMatrixValuesUnipotentDiagonal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCuspSpaceBot
open ValuativeRel Matrix MeasureTheory
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.LocLanglands GlobalTheory.GamMul DiscreteGroups.sglob.LConv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.block_matrix_values_unipotent_diagonal : ∀ (R : Type) [CommRing R] (n o₁ o₂ p q : ℕ), (∀ X : Matrix (Fin p) (Fin q) R, (o₁ + p ≤ o₂ ∨ o₂ + q ≤ o₁) → (uni n o₁ o₂ X).val = 1 + put n o₁ o₂ X ∧ (uni n o₁ o₂ X)⁻¹.val = 1 - put n o₁ o₂ X) ∧ (∀ g : GL (Fin p) R, o₁ + p ≤ n → (dg n o₁ g).val = 1 - eye R n o₁ o₁ p + put n o₁ o₁ g.val ∧ (dg n o₁ g)⁻¹.val = 1 - eye R n o₁ o₁ p + put n o₁ o₁ g⁻¹.val) ∧ (p ≤ n → (shuf R n p).val = eye R n 0 p (n - p) + eye R n (n - p) 0 p ∧ (shuf R n p)⁻¹.val = eye R n p 0 (n - p) + eye R n 0 (n - p) p) := by
  first | exact @GlobalTheory.GamMul.val_uni_dg_shuf | exact GlobalTheory.GamMul.val_uni_dg_shuf | (intros; apply GlobalTheory.GamMul.val_uni_dg_shuf <;> assumption)
