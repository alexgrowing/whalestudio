import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TendstoMobCodiscreteWithin
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModQPrin
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModJTau
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tendsto_mob_codiscreteWithin_codiscreteWithin : ∀ g : GQ, Filter.Tendsto (mob g) (Filter.codiscreteWithin Hs) (Filter.codiscreteWithin Hs) := by
  first | exact @GlobalTheory.FN.tendsto_mob_codiscreteWithin | exact GlobalTheory.FN.tendsto_mob_codiscreteWithin | (intros; apply GlobalTheory.FN.tendsto_mob_codiscreteWithin <;> assumption)
