import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.MemSpanStandardIffProjZero

noncomputable section

namespace Formalism.InvariantFactorPaths.ColumnFamilies

theorem filtration_criterion_of : LemmaA → FiltrationGenericPointCriterion :=
  fun hA n _ M CF pi hpi F _ x => mem_span_standard_iff_proj_zero hA CF pi hpi F x

end Formalism.InvariantFactorPaths.ColumnFamilies
