import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.MeasurePrjFPreimage
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.IsHermNDOfSetting
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.SplitG

noncomputable section

open MeasureTheory NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
  Formalism.L2.SG.TypedSets
open scoped TensorProduct

namespace MassDataMassesW

theorem stabFinite_of (hH : HinfCompact) (hK : KCompactOpen) : StabFinite := by
  intro D X u x
  obtain ⟨e, he⟩ := splitIso_holds X.B.I.cm.sig X.B.I.J
  have hcK := (hK X).1
  have hcI : IsCompact ((Hsub (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u) :
      Set (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J))) := by
    haveI := hH X u
    exact isCompact_iff_compactSpace.2 this
  have homogComponent_comm_second_action : IsCompact ((fun k => (x : HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J) * k *
      (x : HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J)⁻¹) '' (KX X : Set (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J))) :=
    hcK.image ((continuous_const.mul continuous_id).mul continuous_const)
  have hcK3 : IsCompact (e ⁻¹' ((Hsub (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u) :
      Set (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J)) ×ˢ
        ((fun k => (x : HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J) * k *
          (x : HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J)⁻¹) '' (KX X : Set (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J))))) :=
    e.toHomeomorph.isCompact_preimage.2 (hcI.prod homogComponent_comm_second_action)
  haveI hdisc : DiscreteTopology ↥(show Subgroup (HA (AF X.B.I.F) X.B.I.cm.sig X.B.I.J) from
      HFinIn (AF X.B.I.F) X.B.I.cm.sig X.B.I.J) := discHF_setting X
  have pullback_fin_relation : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (Γ : Subgroup G)
      [DiscreteTopology Γ] (K : Set G), IsCompact K → Finite ↥((Subtype.val : Γ → G) ⁻¹' K) := by
    intro G _ _ _ Γ _ K hK
    obtain ⟨U, hU, hUeq⟩ := isOpen_induced_iff.1 (isOpen_discrete ({1} : Set Γ))
    have h1U : (1 : G) ∈ U := by
      have h0 : (1 : Γ) ∈ (Subtype.val : Γ → G) ⁻¹' U := by rw [hUeq]; exact Set.mem_singleton 1
      exact h0
    have hc : Continuous (fun p : G × G => p.1⁻¹ * p.2) := continuous_fst.inv.mul continuous_snd
    have hpre : (fun p : G × G => p.1⁻¹ * p.2) ⁻¹' U ∈ nhds ((1 : G), (1 : G)) := by
      apply hc.continuousAt.preimage_mem_nhds
      simpa using hU.mem_nhds h1U
    obtain ⟨V1, hV1, V2, hV2, hVV⟩ := mem_nhds_prod_iff.1 hpre
    have hV1m : (1 : G) ∈ interior (V1 ∩ V2) := mem_interior_iff_mem_nhds.2 (Filter.inter_mem hV1 hV2)
    obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun k : K => (fun y => (k : G)⁻¹ * y) ⁻¹' interior (V1 ∩ V2))
      (fun k => isOpen_interior.preimage (continuous_const.mul continuous_id)) (by
        intro y hy
        exact Set.mem_iUnion.2 ⟨⟨y, hy⟩, by rw [Set.mem_preimage, inv_mul_cancel]; exact hV1m⟩)
    have hch : ∀ s : ↥((Subtype.val : Γ → G) ⁻¹' K), ∃ i : t,
        ((((i : K) : G))⁻¹ * ((s : Γ) : G)) ∈ interior (V1 ∩ V2) := by
      intro s
      obtain ⟨i, hi, hs⟩ := Set.mem_iUnion₂.1 (ht s.2)
      exact ⟨⟨i, hi⟩, hs⟩
    choose f hf using hch
    refine Finite.of_injective f (fun s1 s2 h => ?_)
    have a1 := hf s1
    have a2 := hf s2
    rw [h] at a1
    have hmem : ((((f s2 : K) : G))⁻¹ * ((s1 : Γ) : G), (((f s2 : K) : G))⁻¹ * ((s2 : Γ) : G)) ∈ V1 ×ˢ V2 :=
      ⟨(interior_subset a1).1, (interior_subset a2).2⟩
    have hU' : ((((f s2 : K) : G))⁻¹ * ((s1 : Γ) : G))⁻¹ * ((((f s2 : K) : G))⁻¹ * ((s2 : Γ) : G)) ∈ U :=
      hVV hmem
    rw [show ((((f s2 : K) : G))⁻¹ * ((s1 : Γ) : G))⁻¹ * ((((f s2 : K) : G))⁻¹ * ((s2 : Γ) : G)) =
      ((s1 : Γ) : G)⁻¹ * ((s2 : Γ) : G) by group] at hU'
    have e1 : ((s1 : Γ)⁻¹ * (s2 : Γ) : Γ) ∈ (Subtype.val : Γ → G) ⁻¹' U := hU'
    rw [hUeq, Set.mem_singleton_iff, inv_mul_eq_one] at e1
    exact Subtype.ext e1
  haveI := pullback_fin_relation _ (show Subgroup (HA (AF X.B.I.F) X.B.I.cm.sig X.B.I.J) from
    HFinIn (AF X.B.I.F) X.B.I.cm.sig X.B.I.J) _ hcK3
  have hsurj : ∀ t : ↥(GamH X u ⊓ (KH X u).map (MulAut.conj x).toMonoidHom),
      ∃ γ : Hsub (AF X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u),
        γ ∈ ratOf (K := Hsub (AF X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u)) ∧
          prjF X.B.I.cm.sig X.B.I.J (frameOf X u) γ = t := by
    intro t
    have ht : (t : Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u)) ∈
        (ratOf (K := Hsub (AF X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u))).map
          (prjF X.B.I.cm.sig X.B.I.J (frameOf X u)) := by
      rw [prjF_map_ratOf]
      exact t.2.1
    obtain ⟨γ, hγ, hγt⟩ := Subgroup.mem_map.1 ht
    exact ⟨γ, hγ, hγt⟩
  choose γ hγ hγt using hsurj
  refine Finite.of_injective (fun t => (⟨⟨(γ t : HA (AF X.B.I.F) X.B.I.cm.sig X.B.I.J),
    Subgroup.mem_comap.1 (hγ t)⟩, ?_⟩ : ((↑) ⁻¹' (e ⁻¹' ((Hsub (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u) :
      Set (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J)) ×ˢ
        ((fun k => (x : HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J) * k *
          (x : HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J)⁻¹) '' (KX X : Set (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J))))) :
      Set ↥(show Subgroup (HA (AF X.B.I.F) X.B.I.cm.sig X.B.I.J) from HFinIn (AF X.B.I.F) X.B.I.cm.sig X.B.I.J)))) ?_
  · simp only [Set.mem_preimage]
    rw [he]
    refine ⟨?_, ?_⟩
    · exact haMap_stabT X.B.I.cm.sig X.B.I.J (fstA X.B.I.F) (tupH (frameOf X u)) (γ t) (γ t).2
    · show (splitA X.B.I.cm.sig X.B.I.J (γ t : HA (AF X.B.I.F) X.B.I.cm.sig X.B.I.J)).2 ∈
        (_ : Set (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J))
      rw [← prjF_val, hγt t]
      obtain ⟨k, hk, hkt⟩ := Subgroup.mem_map.1 t.2.2
      rw [← hkt]
      refine ⟨(k : HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J), Subgroup.mem_subgroupOf.1 hk, ?_⟩
      simp [MulAut.conj_apply]
  · intro t1 t2 h
    have h1 : (γ t1 : HA (AF X.B.I.F) X.B.I.cm.sig X.B.I.J) = γ t2 := by
      have h0 := congrArg (fun z => z.1.1) h
      simpa using h0
    have h2 : γ t1 = γ t2 := Subtype.ext h1
    apply Subtype.ext
    rw [← hγt t1, ← hγt t2, h2]

end MassDataMassesW
