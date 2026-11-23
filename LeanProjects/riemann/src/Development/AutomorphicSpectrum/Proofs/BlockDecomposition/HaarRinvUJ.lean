import Mathlib
import Formalism.RealPlaceAnalysis.InstMeasurableSpaceUJ
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ModularCharacterEqOneOnExpHermitian

open MeasureTheory

namespace GlobalTheory.CompanionTheory.HaarUJ

theorem haar_rinv_UJ : ∀ (n : ℕ) (ε : Fin n → Bool) (μ : Measure (Formalism.REAL.UJ ε)) [μ.IsHaarMeasure],
    μ.IsMulRightInvariant := by
  intro n ε μ _
  have hν : (Formalism.REAL.muG ε).IsMulRightInvariant := ⟨fun g => Formalism.REAL.indefinite_unitary_unimodular n ε g⟩
  have hμ : μ = Measure.haarScalarFactor μ (Formalism.REAL.muG ε) • Formalism.REAL.muG ε :=
    Measure.isMulLeftInvariant_eq_smul μ (Formalism.REAL.muG ε)
  refine ⟨fun g => ?_⟩
  rw [hμ, Measure.map_smul, map_mul_right_eq_self]

end GlobalTheory.CompanionTheory.HaarUJ
