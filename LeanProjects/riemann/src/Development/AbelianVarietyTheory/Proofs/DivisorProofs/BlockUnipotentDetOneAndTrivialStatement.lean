import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockUnipotentDetOneAndTrivial
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCuspSpaceBot
open ValuativeRel Matrix MeasureTheory
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.LocLanglands GlobalTheory.GamMul DiscreteGroups.sglob.LConv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.block_unipotent_det_one_and_trivial : ∀ (R : Type) [CommRing R] (n o₁ o₂ p q : ℕ), ((o₁ + p ≤ o₂ ∨ o₂ + q ≤ o₁) → (∀ X Y : Matrix (Fin p) (Fin q) R, uni n o₁ o₂ (X + Y) = uni n o₁ o₂ X * uni n o₁ o₂ Y) ∧ (∀ X : Matrix (Fin p) (Fin q) R, GeneralLinearGroup.det (uni n o₁ o₂ X) = 1)) ∧ uni n o₁ o₂ (0 : Matrix (Fin p) (Fin q) R) = 1 ∧ (∀ X : Matrix (Fin p) (Fin q) R, (p = 0 ∨ q = 0) → uni n o₁ o₂ X = 1) ∧ dg n o₁ (1 : GL (Fin p) R) = 1 ∧ (o₁ + p ≤ n → (∀ g g' : GL (Fin p) R, dg n o₁ (g * g') = dg n o₁ g * dg n o₁ g') ∧ ∀ g : GL (Fin p) R, GeneralLinearGroup.det (dg n o₁ g) = GeneralLinearGroup.det g) ∧ (∀ (h : p + q = n) (a : GL (Fin p) R) (b : GL (Fin q) R), dg n 0 a * dg n p b = emb₂ R (stdSum h) (a, b)) ∧ shuf R n 0 = 1 ∧ (∀ g : GL (Fin n) R, dg n 0 g = g) := by
  first | exact @GlobalTheory.GamMul.uni_dg_hom | exact GlobalTheory.GamMul.uni_dg_hom | (intros; apply GlobalTheory.GamMul.uni_dg_hom <;> assumption)
