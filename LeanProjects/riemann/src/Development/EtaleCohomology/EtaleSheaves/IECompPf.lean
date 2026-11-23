import Development.EtaleCohomology.EtaleSheaves.EtaleBaseChangeFractionFieldIndEtaleOverPolynomi

noncomputable section
open CategoryTheory Limits

namespace LateralTheory.E.IECompPf
open LateralTheory.E.t_E3Cut

def UnderFA : Prop := ∀ X : CommRingCat.{0}, IsFinitelyAccessibleCategory.{0} (Under X)

def EtSpreads : Prop := MorphismProperty.PreIndSpreads.{0} Et

theorem et_comp : Et.IsStableUnderComposition where
  comp_mem f g hf hg := by
    show (f ≫ g).hom.Etale
    rw [CommRingCat.hom_comp]
    exact RingHom.Etale.stableUnderComposition _ _ hf hg

theorem et_cobase : Et.IsStableUnderCobaseChange :=
  (RingHom.isStableUnderCobaseChange_toMorphismProperty_iff).2 RingHom.Etale.isStableUnderBaseChange

theorem et_fp : Et ≤ MorphismProperty.isFinitelyPresentable.{0} CommRingCat.{0} := fun _ _ f hf =>
  CommRingCat.isFinitelyPresentable_hom f (RingHom.Etale.iff_flat_and_formallyUnramified.1 hf).2.2

theorem IEComp_of (h1 : UnderFA) (h2 : EtSpreads) : IEComp := by
  intro A B C f g hf hg
  have : ∀ X : CommRingCat.{0}, IsFinitelyAccessibleCategory.{0} (Under X) := h1
  have : MorphismProperty.PreIndSpreads.{0} Et := h2
  have := et_comp
  have := et_cobase
  have := MorphismProperty.IsStableUnderComposition.ind_of_preIndSpreads (P := Et) et_fp
  exact this.comp_mem f g hf hg

end LateralTheory.E.IECompPf
