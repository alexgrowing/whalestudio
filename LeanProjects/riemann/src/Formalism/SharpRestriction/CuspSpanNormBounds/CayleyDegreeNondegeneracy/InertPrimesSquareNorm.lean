import Formalism.HermitianLattices.StatementMass
import Formalism.HermitianLattices.StatementLat

noncomputable section

namespace Formalism.MainNotions.BridgeLemma₂

open NumberField IsDedekindDomain

def InertPrimesSquareNorm : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E], Formalism.HermitianLatticesTheory.IsCMUnram E →
    ∀ P : HeightOneSpectrum (𝓞 E), Formalism.HermitianLatticesTheory.conjIdeal (K := E) P.asIdeal = P.asIdeal → IsSquare (Ideal.absNorm P.asIdeal)

end Formalism.MainNotions.BridgeLemma₂

end
