import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WachRingFactsUnramifiedLevelOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankOfMulEqOne
open NumberField PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors Formalism.CohomologicalDescent.FrobeniusPeriodChange IsLocalRing GlobalTheory.WachPlace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wachRingFacts_unramified_levelOne : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (H : LocHW l P) (K LL : FinExt l) (hA : CaseA K LL), RingFacts (H.W K 1 LL hA.2.2) := by
  first | exact @GlobalTheory.WachPlace.ringFacts_of_caseA | exact GlobalTheory.WachPlace.ringFacts_of_caseA | (intros; apply GlobalTheory.WachPlace.ringFacts_of_caseA <;> assumption)
