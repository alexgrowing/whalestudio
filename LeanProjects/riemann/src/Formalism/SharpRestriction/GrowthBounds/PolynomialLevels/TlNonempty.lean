import Formalism.SharpRestriction.GrowthBounds.PlaneCoefficients.PlaneCoeffOneTTens
import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.ValuationOneEqZero

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.NormalSetCounting

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords Formalism.MainNotions.Proposition5Numerics Formalism.MainNotions.PairMembershipBlocks

instance tlNonempty {J r : ℕ} [NeZero J] [NeZero r] (nL : ZMod J → ℕ) : Nonempty (TL J nL r) :=
  ⟨⟨0, Sum.inr 0⟩⟩

def gT {n' r : ℕ} [NeZero n'] [NeZero r] (Fr : Frames n' r) {J : ℕ} [NeZero J] (nL : ZMod J → ℕ) : ℤ → TL J nL r :=
  Function.invFun (posTL Fr)

def Rn {n' r : ℕ} [NeZero n'] [NeZero r] (Fr : Frames n' r) {J : ℕ} [NeZero J] (nL : ZMod J → ℕ) {K : ℕ}
    {O : Type} [CommRing O] [IsDomain O] (A : MvPolynomial (ℤ × Fin K) O) : MvPolynomial (TL J nL r × Fin K) (KK O) :=
  rename (fun v : ℤ × Fin K => (gT Fr nL v.1, v.2)) (MvPolynomial.map (algebraMap O (KK O)) A)

end Formalism.MainNotions.NormalSetCounting
