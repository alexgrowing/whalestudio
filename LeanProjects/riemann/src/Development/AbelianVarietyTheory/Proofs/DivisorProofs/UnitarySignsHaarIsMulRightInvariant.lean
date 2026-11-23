import Mathlib
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ModularCharacterEqOneOnExpHermitian

namespace GlobalTheory

open MeasureTheory

theorem unitarySigns_haar_isMulRightInvariant :
    ∀ (n : ℕ) (ε : Fin n → Bool) (μ : MeasureTheory.Measure (Formalism.REAL.UJ ε)) [μ.IsHaarMeasure],
      μ.IsMulRightInvariant := by
  intro n ε μ _
  haveI : (Formalism.REAL.muG ε).IsMulRightInvariant := ⟨fun g => Formalism.REAL.indefinite_unitary_unimodular _ _ g⟩
  rw [Measure.isMulLeftInvariant_eq_smul μ (Formalism.REAL.muG ε)]
  infer_instance

end GlobalTheory
