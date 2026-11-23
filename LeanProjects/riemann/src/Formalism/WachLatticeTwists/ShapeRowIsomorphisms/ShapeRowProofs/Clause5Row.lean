import Formalism.WachLatticeTwists.ShapeRowIsomorphisms.StatClause5Row
import ReciprocityTheory.ReductiveGroups.TraceFormulas.ImportsAlt
import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatReal

variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

open Formalism.NG
open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC Formalism.RepresentationBoundsCohomology.JT Formalism.RepresentationBoundsCohomology.BR

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology

set_option maxHeartbeats 1000000 in
theorem kRow_rel {O Γ VT VT' : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
    [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)]
    [Group Γ] [TopologicalSpace Γ]
    [AddCommGroup VT] [Module O VT] [TopologicalSpace VT] [IsTopologicalAddGroup VT] [ContinuousSMul O VT]
    [AddCommGroup VT'] [Module O VT'] [TopologicalSpace VT'] [IsTopologicalAddGroup VT'] [ContinuousSMul O VT']
    (D : LatData O Γ VT VT') {M : Type} [AddCommGroup M] [Module O M] (ρM : Representation O Γ M)
    (u : M ≃ₗ[O] (VT ⧸ D.T)) (hu : ∀ g m, u (ρM g m) = D.ρA g (u m)) (x : Z1 D.ρA) (b : coZ1s ρM)
    (hy : kRow D ρM u hu (Submodule.Quotient.mk x) = Submodule.mkQ _ b) :
    ∃ m' : VT ⧸ D.T, ∀ g, u ((b : Γ → M) g) = x.1 g - (D.ρA g m' - m') := by
  have hsym : ∀ g y, u.symm (D.ρA g y) = ρM g (u.symm y) := fun g y => by
    rw [LinearEquiv.symm_apply_eq, hu, LinearEquiv.apply_symm_apply]
  let b' : coZ1s ρM := ⟨fun g => u.symm (x.1 g), fun g h => by
    show u.symm (x.1 (g * h)) = u.symm (x.1 g) + ρM g (u.symm (x.1 h))
    rw [((mem_Z1_iff_cocycle _ _).1 x.2).2 g h, map_add, hsym]⟩
  have hk0 : kRow D ρM u hu (Submodule.Quotient.mk x) = Submodule.mkQ _ b' := rfl
  have hy' : Submodule.mkQ _ b' = Submodule.mkQ _ b := hk0.symm.trans hy
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, Submodule.mem_comap,
    coB1, LinearMap.mem_range] at hy'
  obtain ⟨m, hm⟩ := hy'
  refine ⟨u m, fun g => ?_⟩
  have h1 := congrFun hm g
  rw [Submodule.coe_subtype, Submodule.coe_sub, Pi.sub_apply] at h1
  have h2 : ρM g m - m = u.symm (x.1 g) - (b : Γ → M) g := h1
  have h3 : (b : Γ → M) g = u.symm (x.1 g) - (ρM g m - m) := by rw [h2]; abel
  rw [h3, map_sub, map_sub, LinearEquiv.apply_symm_apply, hu]

set_option maxHeartbeats 1000000 in
theorem clause5Gen {O Γ VT VT' : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
    [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)]
    [Group Γ] [TopologicalSpace Γ]
    [AddCommGroup VT] [Module O VT] [TopologicalSpace VT] [IsTopologicalAddGroup VT] [ContinuousSMul O VT]
    [AddCommGroup VT'] [Module O VT'] [TopologicalSpace VT'] [IsTopologicalAddGroup VT'] [ContinuousSMul O VT']
    (D : LatData O Γ VT VT') {M : Type} [AddCommGroup M] [Module O M] (ρM : Representation O Γ M)
    (u : M ≃ₗ[O] (VT ⧸ D.T)) (hu : ∀ g m, u (ρM g m) = D.ρA g (u m)) (hA : ContAction D.ρA)
    (hk : Function.Injective (kRow D ρM u hu)) (b : coZ1s ρM)
    (hb : Submodule.mkQ _ b ∈ LinearMap.range (kRow D ρM u hu)) (t : Γ → D.T') (ht : t ∈ Z1 D.ρTl')
    (c : Γ → KO O) (hc : Continuous c)
    (h : ∀ g k, pairKO D.bT D.T (D.ρA g (u ((b : Γ → M) k))) (t g) =
      ((D.ε g : Oˣ) : O) • c k - c (g * k) + c g) :
    prK D _ hk ⟨Submodule.mkQ _ b, hb⟩ (Submodule.Quotient.mk ⟨t, ht⟩) = 0 := by
  have hb0 := hb
  obtain ⟨y, hy⟩ := hb0
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  obtain ⟨m', hbg⟩ := kRow_rel D _ u hu x b hy
  have hx' : (fun g => u ((b : Γ → M) g)) ∈ Z1 D.ρA := by
    refine (mem_Z1_iff_cocycle _ _).2 ⟨?_, fun g h => ?_⟩
    · have hxc : Continuous x.1 := ((mem_Z1_iff_cocycle _ _).1 x.2).1
      have hc2 : Continuous fun g : Γ => D.ρA g m' := hA.comp (continuous_id.prodMk continuous_const)
      have : (fun g => u ((b : Γ → M) g)) = fun g => x.1 g - (D.ρA g m' - m') := funext hbg
      rw [this]
      exact hxc.sub (hc2.sub continuous_const)
    · rw [b.2 g h, map_add, hu]
  have hxx : (Submodule.Quotient.mk x : ReciprocityTheory.Gal.H1 D.ρA) = Submodule.Quotient.mk ⟨_, hx'⟩ := by
    refine (Submodule.Quotient.eq _).2 ((mem_coboundaries1 _ _).2 ⟨m', fun g => ?_⟩)
    change x.1 g - u ((b : Γ → M) g) = _
    rw [hbg]; abel
  have e1 : (⟨Submodule.mkQ _ b, hb⟩ : LinearMap.range (kRow D _ u hu)) =
      LinearEquiv.ofInjective _ hk (Submodule.Quotient.mk x) := Subtype.ext hy.symm
  rw [e1]
  change D.pr ((LinearEquiv.ofInjective _ hk).symm (LinearEquiv.ofInjective _ hk (Submodule.Quotient.mk x))) _ = 0
  rw [LinearEquiv.symm_apply_apply, hxx]
  exact ReciprocityTheory.ChartRestriction.T2.pr_eq_zero_of_swap_cob D ⟨_, hx'⟩ ⟨_, ht⟩ c hc h

theorem clause5Row : StatClause5Row := by
  intro O _ _ _ _ _ _ _ VT VT' _ _ _ _ _ _ _ _ _ _ A T' G _ _ _ _ _ M _ _ _ _ r χ Dw _ ε T₁ T₂ _ _ _ _ ρ₁ ρ₂ π γ
    D u hu v hε hT hπ hv hγ hk C₁ hC a b hb ha hCa ⟨c, hc, hcob⟩
  have ht : (fun g => v (π (a g))) ∈ Z1 D.ρTl' := by
    refine (mem_Z1_iff_cocycle _ _).2 ⟨hC a hCa, fun g h => ?_⟩
    have e1 : a (g * h) = a g + ρ₁ (g : G) (a h) := ha g h
    rw [e1, map_add, map_add, hπ, hv]
  have e2 : clsRow D v (fun g => π (a g)) = Submodule.Quotient.mk ⟨_, ht⟩ := by
    unfold clsRow
    exact dif_pos ht
  rw [e2]
  refine clause5Gen D _ u hu (ReciprocityTheory.ChartRestriction.T2.contAction_quotient hT D.T D.stT) hk b hb _ ht c hc fun g k => ?_
  have h4 := hcob g k
  rw [hγ] at h4
  have h5 : u (uElt r χ (g : G) • (b : Dw → M) k) = D.ρA g (u ((b : Dw → M) k)) := hu g _
  rw [h5] at h4
  rw [hε g]
  exact h4

end Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology
