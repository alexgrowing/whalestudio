import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GeometricLemmaOfFiltration
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GeometricLemmaFiltration
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.geometricLemma_of_bzFiniteness_of_filtration : GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.GeometricLemmaFiltration → GlobalTheory.Published.GeometricLemma := by
  first | exact @GlobalTheory.geometricLemma_of_filtration | exact GlobalTheory.geometricLemma_of_filtration | (intros; apply GlobalTheory.geometricLemma_of_filtration <;> assumption)
