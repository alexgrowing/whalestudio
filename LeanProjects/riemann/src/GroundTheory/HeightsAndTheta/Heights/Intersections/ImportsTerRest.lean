import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.LocRing
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def regularityLocalResidue_holds.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι))
    (s : MRing ι) (a : K → ℕ) (W : Ideal (MRing ι)) (b : Fin 0 → K → ℤ),
    IsArithVar P 1 → IsMultiHomog s a → s ∉ P → W ∈ divSupp P s → ∀ [IsLocalRing (locRing P W)],
    Finite (IsLocalRing.ResidueField (locRing P W)) ∧
      Nat.card (IsLocalRing.ResidueField (locRing P W)) = charOf W ^ (geoNum 0 W b).toNat

end

end GroundTheory.Heights₂.Heights.Inter
