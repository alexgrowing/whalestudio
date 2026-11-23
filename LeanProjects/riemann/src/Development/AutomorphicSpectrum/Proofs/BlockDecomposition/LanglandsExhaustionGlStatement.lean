import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LanglandsExhaustionGl
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyInterleaving.LInjective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsMultisegments
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsExhaustionGL
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.langlands_multisegments_of_exhaustion_gl : (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) → (∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], LSocleGL k) → (∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], LSegJacquet k) → (∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], LOrderFree k) → GlobalTheory.Published.LanglandsExhaustionGL → GlobalTheory.Published.LanglandsMultisegments := by
  first | exact @GlobalTheory.CompanionTheory.LanglandsMultiseg.langlandsMultisegments_of_clauses | exact GlobalTheory.CompanionTheory.LanglandsMultiseg.langlandsMultisegments_of_clauses | (intros; apply GlobalTheory.CompanionTheory.LanglandsMultiseg.langlandsMultisegments_of_clauses <;> assumption)
