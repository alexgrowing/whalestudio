import Mathlib
import Formalism.SharpRestriction.InertJacobiLevels.ExtraFinal
import Development.AutomorphicSpectrum.Proofs.JetProofs.ExistsDiagonalCongrOfSimilitudeDistinctEigenvalu
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.MassIntegralStmt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqUniqueOfClassification
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowHCParameterIsHCParamAndFormalDegreePos

namespace GlobalTheory.CompanionTheory.Front

theorem discreteSeriesUpqUnique : GlobalTheory.Published.DiscreteSeriesUpqUnique := by
  have h := GlobalTheory.CompanionTheory.DS.dsUnique
  unfold GlobalTheory.CompanionTheory.DS.DSUnique at h
  unfold GlobalTheory.Published.DiscreteSeriesUpqUnique
  intros
  apply h <;> assumption

end GlobalTheory.CompanionTheory.Front
