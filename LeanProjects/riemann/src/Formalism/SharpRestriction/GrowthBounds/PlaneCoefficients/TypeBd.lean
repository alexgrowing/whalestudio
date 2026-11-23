import Formalism.SharpRestriction.GrowthBounds.TwistedSubstitution.TypeBound
import Formalism.SharpRestriction.GrowthBounds.GLWeightTheory

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.PairMembershipBlocks

open Formalism.MainNotions.G Formalism.MainNotions.TestSideWords Formalism.MainNotions.G.GLWeightTheory

theorem typeBound_proved (D : Formalism.BasicNotions.D7) : TypeBound := by

  have hV := Formalism.MainNotions.G.GLWeightTheory.valuation_field D
  unfold Formalism.MainNotions.CovariantDegrees.ValuationLemmaField Formalism.MainNotions.CovariantDegrees.ShaLengthVersionTwo at hV
  unfold TypeBound
  intro K _ _ ι _ LL n _ S e he _ G lam hne
  obtain ⟨hval, hlam⟩ := hV.2 K ι LL n S e he
  exact ⟨fun M hM => (hlam G M).1 hM lam hne, fun th hth => (hval G th).1 hth lam hne⟩

end Formalism.MainNotions.PairMembershipBlocks
