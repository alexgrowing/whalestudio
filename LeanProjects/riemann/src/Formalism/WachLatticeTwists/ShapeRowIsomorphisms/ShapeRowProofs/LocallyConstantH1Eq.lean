import Formalism.WachLatticeTwists.ShapeRowIsomorphisms.Statement
import Formalism.WachLatticeTwists.CharacterSplitJumps.CharacterJumpProofs.InChiSplit

variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

open Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.RepresentationBoundsCohomology.JT
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open ReciprocityTheory.ChartRestriction.T2 (GK PadicCoeff FracTop IsCyc IsCycOn)

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology

theorem locallyConstantH1_eq {O Γ M : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] [AddCommGroup M] [Module O M]
    (ρ : Representation O Γ M) : lcH1 ρ = ReciprocityTheory.ChartRestriction.T2.HcLC ρ := rfl

theorem shapeRow : StatShapeRow := by
  intro p _ K O _ _ _ _ _ _ _ A T' G _ _ _ _ _ M _ _ _ _ r χ Dw _ ε e hK hO hF i hε ⟨u⟩ hact
  constructor
  · intro he
    rw [locallyConstantH1_eq]
    exact ReciprocityTheory.ChartRestriction.T2.quotShape_G hK hO hF i (ε := ε.comp Dw.subtype) hε e he u _
      (fun g m => hact g.1 g.2 m)
  · intro he I hI
    subst he
    rw [locallyConstantH1_eq]
    exact ReciprocityTheory.ChartRestriction.T2.quotShape_G_unr hK hO hF i u _
      (fun g m => by
        have := hact g.1 g.2 m
        simp only [pow_zero, inv_one, Units.val_one, one_smul] at this
        exact this) I hI

theorem shapeDec : StatShapeDec := by
  intro p _ O _ _ _ _ _ hinj E Ω _ _ _ _ _ Aw hp v hv A T' _ _ _ _ M _ _ _ _ r χ ε e hε hM hact
  obtain ⟨K, hK, i, h1, h2, h3⟩ := ReciprocityTheory.ChartRestriction.T2.exists_dec_equiv (F := E) Aw hp
  obtain ⟨_, _, _, _, hO, hF⟩ := hT2Core.out.top p O hinj
  have h := shapeRow p K O A T' (Ω ≃ₐ[E] Ω) M r χ (Aw.decompositionSubgroup E) ε e hK hO hF i
    (h1 O _ hε) hM hact
  rw [h3 v hv] at h
  refine ⟨h.1, fun he => h.2 he _ fun g => ?_⟩
  rw [h2 g, Subgroup.mem_subgroupOf]

end Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology
