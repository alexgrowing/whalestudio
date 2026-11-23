import Mathlib
import ReciprocityTheory.ResidueCardinality.ArtinOntoB

noncomputable section

namespace ReciprocityTheory.DiscreteGroups.GlobalClassField

open NumberField IsDedekindDomain

theorem ul_card_residue_eq (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers F)) =
      Ideal.absNorm v.asIdeal := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  exact ReciprocityTheory.Bridge.ResidueFieldCardinality.card_residue v

end ReciprocityTheory.DiscreteGroups.GlobalClassField
