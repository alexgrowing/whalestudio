import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeierstrassConstantQExpansion
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weierstrass_constant_q_expansion : ∀ (N : ℕ) [NeZero N], HasQ N gN (cG N) := by
  first | exact @GlobalTheory.WpFam.hasQ_gN | exact GlobalTheory.WpFam.hasQ_gN | (intros; apply GlobalTheory.WpFam.hasQ_gN <;> assumption)
