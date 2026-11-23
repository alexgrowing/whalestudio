import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeierstrassPTorsionIsModularFamily
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weierstrassP_torsion_isModularFamily : ∀ (N : ℕ) [NeZero N], IsFam (vact N) 2 (wp N) ∧ IsFam (vact N) 3 (wpd N) := by
  first | exact @GlobalTheory.WpFam.isFam_wp_wpd | exact GlobalTheory.WpFam.isFam_wp_wpd | (intros; apply GlobalTheory.WpFam.isFam_wp_wpd <;> assumption)
