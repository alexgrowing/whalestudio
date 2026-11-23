import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsUnimodularMulEqNegOfIndependentModMaximal
import Formalism.LocalToGlobal.CharacterGerms.LatticeInclusionFormsInjective
import Formalism.LocalToGlobal.CharacterGerms.CartesianBoundOnCurves
import Formalism.LocalToGlobal.CharacterGerms.CoeffIterateZero
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.TwoMulChainStartIndexAddOneOfOdd
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unimodular_mul_eq_neg_of_independent_mod_maximal : ∀ (C : Type) [Field C] (V : VF C) (n n0 : ℕ) (Φ : Fin n → Fin n0 → C), (∀ b c, V.Ge 0 (Φ b c)) → IndepMod V (fun c b => Φ b c) → n0 ≤ n ∧ ∃ Y : Matrix (Fin n) (Fin n) C, (∀ b b', V.Ge 0 (Y b b')) ∧ V.v Y.det = 0 ∧ ∀ (b : Fin n) (c : Fin n0), b.val < n0 → ∑ b', Y b b' * Φ b' c = if b.val = c.val then -1 else 0 := by
  first | exact @GlobalTheory.exists_unimodular_mul_eq_neg_of_indepMod | exact GlobalTheory.exists_unimodular_mul_eq_neg_of_indepMod | (intros; apply GlobalTheory.exists_unimodular_mul_eq_neg_of_indepMod <;> assumption)
