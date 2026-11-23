import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QExpansionIsAlgebraicWeierstrassTorsion
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.TranslateProduct
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModDefs
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.qExpansion_isAlgebraic_weierstrassTorsion : ∀ (N : ℕ) [NeZero N] (x : Fin 2 → ZMod N), QAll (IsAlgebraic ℚ) N (wp N x) ∧ QAll (IsAlgebraic ℚ) N (wpd N x) ∧ (x ≠ 0 → QAll (IsAlgebraic ℚ) N (wB N x)) := by
  first | exact @GlobalTheory.WpFam.qAll_isAlgebraic_torsion | exact GlobalTheory.WpFam.qAll_isAlgebraic_torsion | (intros; apply GlobalTheory.WpFam.qAll_isAlgebraic_torsion <;> assumption)
