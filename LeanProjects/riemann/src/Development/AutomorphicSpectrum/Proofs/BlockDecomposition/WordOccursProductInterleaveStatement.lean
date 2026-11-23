import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WordOccursProductInterleave
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyInterleaving.LInjective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsMultisegments
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsExhaustionGL
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.word_occurs_product_interleave : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL), ∀ (x y : IrrGL k) (u v w : List (IrrGL k)), (∀ c ∈ u, c.IsCusp) → (∀ c ∈ v, c.IsCusp) → Wd x.rep u → Wd y.rep v → Zc.Comb.Interleave u v w → Wd (prod₂ x.rep y.rep) w := by
  first | exact @GlobalTheory.CompanionTheory.WordProd.wd_prod₂_of_interleave | exact GlobalTheory.CompanionTheory.WordProd.wd_prod₂_of_interleave | (intros; apply GlobalTheory.CompanionTheory.WordProd.wd_prod₂_of_interleave <;> assumption)
