import Formalism.SharpRestriction.GrowthBounds.TwistedSubstitution.Lemma5aGeneratorProducts
import Formalism.SharpRestriction.GrowthBounds.TwistedSubstitution.TransportMon

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.TestSideWords

open Formalism.MainNotions.G Formalism.MainNotions.SourceCleaning Formalism.MainNotions.PlaneGramData Formalism.MainNotions.Pf14

variable {n' r K m : ℕ} [NeZero n'] [NeZero r] [NeZero K] (Fr : Frames n' r) (p : ℕ) (hk : m + 1 = r + K)
  {J : ℕ} [NeZero J] (nL : ZMod J → ℕ)

def RestGeo : Prop :=
  ∀ {n' r : ℕ} [NeZero n'] (Fr : Frames n' r) (L₁ N₁ : ℕ), Fr.Valid L₁ N₁ → ∀ (p : ℕ) {J : ℕ} [NeZero J]
    (nL : ZMod J → ℕ), J = Fr.J → (∀ j, nL j = (Fr.LLset (segZ j)).card) → GeoOK Fr p nL

end Formalism.MainNotions.TestSideWords
