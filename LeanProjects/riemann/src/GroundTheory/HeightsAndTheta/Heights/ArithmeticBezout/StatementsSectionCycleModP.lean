import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsChowDegreeGeoNum
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

namespace ObjectsChow

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsMultiProjPrime)

def SectionCycleModP.Statement : Prop :=
  ∀ (n p : ℕ) (W : Ideal (MRing (PBlk n))) (F : Type) [Field F],
    p.Prime → IsMultiProjPrime W → C (p : ℤ) ∈ W →
      Function.Surjective (Int.castRingHom F) → ((p : ℤ) : F) = 0 →
        ∀ i : Fin n, (X ⟨(), i⟩ : MRing (PBlk n)) ∉ W →
          divCycle ((IndefiniteRowSideFullHecke.ArithBezout.finIdeal W).map (MvPolynomial.map (Int.castRingHom F)))
              (Pi.single i 1) =
            Finsupp.mapDomain
              (fun W' => (IndefiniteRowSideFullHecke.ArithBezout.finIdeal W').map (MvPolynomial.map (Int.castRingHom F)))
              (ReciprocityTheory.ChartRestriction.G.Geo.divCycle W (X ⟨(), i⟩))

end ObjectsChow

end GroundTheory.Heights₂.Heights
