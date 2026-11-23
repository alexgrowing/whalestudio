import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsKodairaGeneric
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.GeneratedModOfSubsingleton
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def FujitaGeneric.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]
    (P : Ideal (MRing ι)) (D : ℕ) (a : K → ℤ),
    IsArithVar P (D + 1) → NefOnGenericDeg P a →
    ∃ m : ℕ, ∀ n i : ℕ, 1 ≤ i →
      Subsingleton (KH.cechHc ι (KH.quotPart ℚ (P.map (MvPolynomial.map (Int.castRingHom ℚ))))
        ((n : ℤ) • a + fun _ => (m : ℤ)) i)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
