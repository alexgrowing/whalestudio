import Mathlib
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.IwaChol
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUpperMulUnitaryComplex

namespace PositivityTheory.Rg.Cz

open Matrix

theorem exists_upper_unitary {ι : Type} {n : ℕ} (y : GL (Fin n) (ι → ℂ)) :
    ∃ (b : GL (Fin n) (ι → ℂ)) (k : Matrix.unitaryGroup (Fin n) (ι → ℂ)),
      (∀ i j : Fin n, j < i → b.val i j = 0) ∧ y = b * Unitary.toUnits k := by
  exact GlobalTheory.CompanionTheory.Iwasawa.exists_upper_mul_unitary y

end PositivityTheory.Rg.Cz
