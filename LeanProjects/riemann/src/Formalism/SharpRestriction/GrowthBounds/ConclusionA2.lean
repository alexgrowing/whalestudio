import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.GrowthBounds.ObjPol

noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.CovariantDegrees

open Formalism.MainNotions.G

def HyperplaneRank (_D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (N n : ℕ) [NeZero n] (LL : Letters (Fin N))
    (B : Fin N → ℕ),
    LinearIndependent O (fun x : {x : PPath n N LL B × (ℤ → Finset (Fin n)) // IsSt x.1.mu x.2} =>
      Psi O x.1.1.mu x.1.2) ∧
    Submodule.span O {G | ∃ P : PPath n N LL B, ∃ I : ℤ → Finset (Fin n), IsSt P.mu I ∧ G = Psi O P.mu I} =
      Pol O n B

end Formalism.MainNotions.CovariantDegrees
