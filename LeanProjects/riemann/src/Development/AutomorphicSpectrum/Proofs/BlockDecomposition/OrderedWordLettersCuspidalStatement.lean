import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrderedWordLettersCuspidal
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyInterleaving.LInjective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsMultisegments
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsExhaustionGL
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ordered_word_letters_cuspidal : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {h : ℕ} (Δ : Fin h → Segment k), ∀ c ∈ wtW Δ, c.IsCusp := by
  first | exact @GlobalTheory.CompanionTheory.ZcWords.wtW_isCusp | exact GlobalTheory.CompanionTheory.ZcWords.wtW_isCusp | (intros; apply GlobalTheory.CompanionTheory.ZcWords.wtW_isCusp <;> assumption)
