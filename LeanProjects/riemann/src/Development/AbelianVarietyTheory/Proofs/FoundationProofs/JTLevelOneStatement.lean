import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.JTLevelOne
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModQPrin
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModJTau
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lv_jT_one_and_jT_smul_eq : ∀ E : Subring ℂ, Lv E 1 1 jT ∧ ∀ (γ : SL(2, ℤ)) (τ : ℍ), jT (γ • τ) = jT τ := by
  first | exact @GlobalTheory.FN.jT_level_one | exact GlobalTheory.FN.jT_level_one | (intros; apply GlobalTheory.FN.jT_level_one <;> assumption)
