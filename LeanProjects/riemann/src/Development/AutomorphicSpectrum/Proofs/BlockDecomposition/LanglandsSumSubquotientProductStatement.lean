import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LanglandsSumSubquotientProduct
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyInterleaving.LInjective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsMultisegments
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsExhaustionGL
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.langlands_sum_subquotient_product : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL), LSocleGL k → LSegJacquet k → LOrderFree k → (∀ x : IrrGL k, ∃ 𝔪 : Multiset (Segment k), IsL 𝔪 x.rep) → ∀ (𝔪 𝔫 : Multiset (Segment k)) (x : Fin 2 → IrrGL k) (y : IrrGL k) (hd : ∑ a, (x a).1 = y.1), IsL 𝔪 (x 0).rep → IsL 𝔫 (x 1).rep → IsL (𝔪 + 𝔫) y.rep → IsSubquotient y.rep (prodIrr x hd) := by
  first | exact @GlobalTheory.CompanionTheory.LangSumSub.main | exact GlobalTheory.CompanionTheory.LangSumSub.main | (intros; apply GlobalTheory.CompanionTheory.LangSumSub.main <;> assumption)
