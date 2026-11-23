import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.QbBasisApply

noncomputable section

namespace Formalism.InvariantFactorPaths.ColumnFamilies

theorem filtration_theorem_one_of : LemmaA → ColumnFamilyStandardVectorsBasis := by
  intro hA n _ M CF
  refine ⟨?_, fun R _ => qb_basisR hA CF R⟩
  have := qb_basisR hA CF ℤ
  rw [qb_vecF_int] at this
  exact this

end Formalism.InvariantFactorPaths.ColumnFamilies
