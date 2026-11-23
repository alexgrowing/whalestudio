import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QConjTorsion
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.qConj_torsion_points : ∀ (N : ℕ) [NeZero N] (g : ℂ ≃+* ℂ) (a : (ZMod N)ˣ), ZetaAct g N a → ∀ x : Fin 2 → ZMod N, QConj g N (wp N x) (wp N (vmul x (dg a))) ∧ QConj g N (wpd N x) (wpd N (vmul x (dg a))) ∧ (x ≠ 0 → QConj g N (wB N x) (wB N (vmul x (dg a)))) := by
  first | exact @GlobalTheory.WpFam.ConjExp.qConj_torsion | exact GlobalTheory.WpFam.ConjExp.qConj_torsion | (intros; apply GlobalTheory.WpFam.ConjExp.qConj_torsion <;> assumption)
