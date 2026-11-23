import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsogenyFormulaWeierstrassPIntegral
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTrSelf
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.TranslateProduct
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModDefs
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isogeny_formula_weierstrassP_integral : ∀ (L : PeriodPair) (α β Ω P : ℂ) (M n : ℕ), MulStable L β → β.im ≠ 0 → Ω ^ 12 = latDisc L → MulStable L α → Complex.normSq α = n → 0 < n → 0 < M → P ∉ L.lattice → (M : ℂ) * P ∈ L.lattice → IsIntegral ℤ (((M * n : ℕ) : ℂ) ^ 2 * ((α ^ 2 - n) * ((s2 L + L.weierstrassP P) / Ω ^ 2) - (α ^ 2 - 1) * (L.weierstrassP P / Ω ^ 2))) := by
  first | exact @GlobalTheory.IsogFormula.main | exact GlobalTheory.IsogFormula.main | (intros; apply GlobalTheory.IsogFormula.main <;> assumption)
