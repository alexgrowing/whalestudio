import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.FramedTwoCoboundaries

noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory Matrix Finset
open scoped InnerProductSpace ENNReal
open Formalism.MainNotions.S Formalism.MainNotions.CayleySignature

namespace BData

variable {X : BData}

theorem integral_tr {P : Mat X.k X.r} {ε : Fin (2 * X.r + X.k + 1) → Bool} (hP : IsCayleyU X.k X.r ε P) {c : ℝ≥0∞}
    (hμ : X.μG = c • (Formalism.REAL.muG ε).map (cayleyEmbedding P)) {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : Formalism.QuantumDeterminants.Mt X.k X.r → E) :
    ∫ x, F x ∂X.μG = c.toReal • ∫ g, F (cayleyEmbedding P g) ∂(Formalism.REAL.muG ε) := by
  rw [hμ, integral_smul_measure, (cayleyEmbedding_measurable hP).integral_map]

end BData

end Formalism.MainNotions.LeviCoordinates

end
