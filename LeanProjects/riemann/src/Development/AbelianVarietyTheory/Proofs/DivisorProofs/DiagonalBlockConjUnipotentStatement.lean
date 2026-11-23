import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlockConjUnipotent
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCuspSpaceBot
open ValuativeRel Matrix MeasureTheory
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.LocLanglands GlobalTheory.GamMul DiscreteGroups.sglob.LConv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.diagonal_block_conj_unipotent : ∀ (R : Type) [CommRing R] (n o₁ o₂ p q : ℕ), (o₁ + p ≤ o₂ ∨ o₂ + q ≤ o₁) → o₁ + p ≤ n → o₂ + q ≤ n → (∀ (g : GL (Fin p) R) (X : Matrix (Fin p) (Fin q) R), dg n o₁ g * uni n o₁ o₂ X = uni n o₁ o₂ (g.val * X) * dg n o₁ g) ∧ (∀ (g : GL (Fin q) R) (X : Matrix (Fin p) (Fin q) R), uni n o₁ o₂ X * dg n o₂ g = dg n o₂ g * uni n o₁ o₂ (X * g.val)) ∧ (∀ (a : GL (Fin p) R) (b : GL (Fin q) R), dg n o₁ a * dg n o₂ b = dg n o₂ b * dg n o₁ a) := by
  first | exact @GlobalTheory.GamMul.dg_uni_comm | exact GlobalTheory.GamMul.dg_uni_comm | (intros; apply GlobalTheory.GamMul.dg_uni_comm <;> assumption)
