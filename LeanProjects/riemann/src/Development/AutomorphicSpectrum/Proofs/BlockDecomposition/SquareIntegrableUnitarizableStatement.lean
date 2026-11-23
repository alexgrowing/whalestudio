import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SquareIntegrableUnitarizable
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanNecTemp
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.PropsCos
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsExhaustionGL
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BernsteinUnitaryProductIrreducible
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.square_integrable_unitarizable : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (x : IrrGL k), IsSqIntCoeff x.rep → IsUnitarisable x.rep := by
  first | exact @GlobalTheory.CompanionTheory.SqIntUnit.isUnitarisable_of_isSqIntCoeff | exact GlobalTheory.CompanionTheory.SqIntUnit.isUnitarisable_of_isSqIntCoeff | (intros; apply GlobalTheory.CompanionTheory.SqIntUnit.isUnitarisable_of_isSqIntCoeff <;> assumption)
