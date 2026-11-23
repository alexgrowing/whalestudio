import Formalism.WachLatticeTwists.RealClassMaps.StatClassMapReal

variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

open Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.RepresentationBoundsCohomology.JT Formalism.RepresentationBoundsCohomology.JS Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC
open ReciprocityTheory.ChartRestriction.T2 (GK PadicCoeff FracTop IsCyc IsCycOn IsFGTop cupFG toH1Cocycles traceH1 transportCocycles)

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.FIN

theorem kRowRange : StatKRowRange := by
  intro O _ _ _ _ _ _ _ VT VT' _ _ _ _ _ _ _ _ _ _ G _ _ D M _ _ ρM u hu hopen
  have hdisc : DiscreteTopology (VT ⧸ D.T) :=
    QuotientAddGroup.discreteTopology (N := D.T.toAddSubgroup) hopen
  apply le_antisymm
  · rintro _ ⟨y, rfl⟩
    induction y using Submodule.Quotient.induction_on with
    | _ c =>
      refine ⟨transportCocycles (MulEquiv.refl G) u ρM D.ρA hu ⟨c.1, c.2.2⟩, ?_, rfl⟩
      have h1 : IsLocallyConstant c.1 := (IsLocallyConstant.iff_continuous _).2 c.2.1
      exact h1.comp u.symm
  · rintro _ ⟨c, hc, rfl⟩
    have hc' : IsLocallyConstant (c : G → M) := hc
    have h3 : (fun g : G => u ((c : G → M) g)) ∈ Z1 D.ρA := by
      refine ⟨(hc'.comp u).continuous, fun a b => ?_⟩
      beta_reduce
      rw [c.2, map_add, hu]
    refine ⟨Submodule.Quotient.mk ⟨_, h3⟩, ?_⟩
    refine congrArg (Submodule.mkQ _) (Subtype.ext (funext fun g => ?_))
    change u.symm (u ((c : G → M) g)) = _
    rw [LinearEquiv.symm_apply_apply]

theorem resLC : StatResLC := by
  intro O G M _ _ _ _ _ ρ Dw
  rintro _ ⟨c, hc, rfl⟩
  have hc' : IsLocallyConstant (c : G → M) := hc
  refine ⟨restrictCocycles1 ρ Dw c, ?_, rfl⟩
  exact hc'.comp_continuous continuous_subtype_val

section
variable {O Γ VT VT' : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
    [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)]
    [Group Γ] [TopologicalSpace Γ]
    [AddCommGroup VT] [Module O VT] [TopologicalSpace VT] [IsTopologicalAddGroup VT] [ContinuousSMul O VT]
    [AddCommGroup VT'] [Module O VT'] [TopologicalSpace VT'] [IsTopologicalAddGroup VT'] [ContinuousSMul O VT']

theorem clsRow_of_mem (D : LatData O Γ VT VT') {T₂ : Type} [AddCommGroup T₂] [Module O T₂] (v : T₂ ≃ₗ[O] D.T')
    (f : Γ → T₂) (h : (fun g => v (f g)) ∈ Z1 D.ρTl') : clsRow D v f = Submodule.Quotient.mk ⟨_, h⟩ :=
  dif_pos h

theorem clsRowV_of_mem (D : LatData O Γ VT VT') {V₂ : Type} [AddCommGroup V₂] [Module O V₂] (w : V₂ ≃ₗ[O] VT')
    (f : Γ → V₂) (h : (fun g => w (f g)) ∈ Z1 D.ρT') : clsRowV D w f = Submodule.Quotient.mk ⟨_, h⟩ :=
  dif_pos h

end

theorem classMapReal : StatClassMapReal := by
  intro O _ _ _ _ _ _ _ VT VT' _ _ _ _ _ _ _ _ _ _ G _ _ D T₂ _ _ ρ₂ v hv Fs
  refine ⟨fun a ha b hb => ?_, fun c a ha => ?_, fun a ha => ?_, fun x _ => ?_⟩
  · have hab : a + b ∈ zcRow D v := add_mem ha hb
    rw [clsRow_of_mem D v _ hab, clsRow_of_mem D v _ ha, clsRow_of_mem D v _ hb, ← Submodule.Quotient.mk_add]
    exact congrArg _ (Subtype.ext (funext fun g => map_add v _ _))
  · have hca : c • a ∈ zcRow D v := Submodule.smul_mem _ c ha
    rw [clsRow_of_mem D v _ hca, clsRow_of_mem D v _ ha, ← Submodule.Quotient.mk_smul]
    exact congrArg _ (Subtype.ext (funext fun g => map_smul v _ _))
  · rw [clsRow_of_mem D v _ ha, Submodule.Quotient.mk_eq_zero]
    constructor
    · intro h
      obtain ⟨m, hm⟩ := (mem_coboundaries1 _ _).1 h
      refine ⟨v.symm m, funext fun g => ?_⟩
      have h1 : v (a g) = D.ρTl' g m - m := hm g
      apply v.injective
      change v (ρ₂ g (v.symm m) - v.symm m) = v (a g)
      rw [map_sub, hv, LinearEquiv.apply_symm_apply, h1]
    · rintro ⟨m, hm⟩
      refine (mem_coboundaries1 _ _).2 ⟨v m, fun g => ?_⟩
      change v (a g) = _
      rw [← hm]
      change v (ρ₂ g m - m) = _
      rw [map_sub, hv]
  · induction x using Submodule.Quotient.induction_on with
    | _ c =>
      have h : (fun g => v (v.symm (c.1 g))) ∈ Z1 D.ρTl' := by
        simpa using c.2
      refine ⟨fun g => v.symm (c.1 g), h, ?_⟩
      rw [clsRow_of_mem D v _ h]
      exact congrArg _ (Subtype.ext (funext fun g => (v.apply_symm_apply _).symm))

theorem clsVReal : StatClsVReal := by
  intro O _ _ _ _ _ _ _ VT VT' _ _ _ _ _ _ _ _ _ _ G _ _ D T₂ V₂ _ _ _ _ ρV iV v w hw hwe a ha
  have ha' : (fun g => v (a g)) ∈ Z1 D.ρTl' := ha
  have h : (fun g => w (iV (a g))) ∈ Z1 D.ρT' := by
    refine ⟨?_, fun g k => ?_⟩
    · simp only [hw]
      exact continuous_subtype_val.comp ha'.1
    · simp only [hw]
      have := congrArg Subtype.val (ha'.2 g k)
      exact this
  rw [clsRow_of_mem D v _ ha, clsRowV_of_mem D w _ h]
  refine ⟨?_, fun h0 => ?_⟩
  · exact congrArg _ (Subtype.ext (funext fun g => (hw (a g)).symm))
  · rw [Submodule.Quotient.mk_eq_zero] at h0
    obtain ⟨m, hm⟩ := (mem_coboundaries1 _ _).1 h0
    refine ⟨w.symm m, funext fun g => ?_⟩
    have h1 : w (iV (a g)) = D.ρT' g m - m := hm g
    apply w.injective
    change w (ρV g (w.symm m) - w.symm m) = _
    rw [map_sub, hwe, LinearEquiv.apply_symm_apply, h1]

end Formalism.RepresentationBoundsCohomology.FIN
