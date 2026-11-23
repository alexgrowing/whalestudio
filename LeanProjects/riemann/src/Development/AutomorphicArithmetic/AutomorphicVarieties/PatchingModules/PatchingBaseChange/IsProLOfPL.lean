import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.AlgebraMapEq
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.PhiFg
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ProBurnside

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa
open scoped TensorProduct

open UpperTheory.V.AlgebraTools in
private theorem isProL_of_PL (l : ℕ) (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
    (H : Subgroup Γ) (hH : IsOpen (H : Set Γ)) (h : PL l H = ⊥) : IsProL l H := by
  classical
  rw [isProL_iff]
  intro N g
  set NΓ : Set Γ := Subtype.val '' ((N.toOpenSubgroup : Subgroup H) : Set H) with hNΓ
  have hNo : IsOpen NΓ := hH.isOpenMap_subtype_val _ N.toOpenSubgroup.isOpen
  have hKc : IsCompact NΓᶜ := hNo.isClosed_compl.isCompact
  let ι := {U : OpenNormalSubgroup Γ // ∀ x ∈ H, ∃ e, x ^ l ^ e ∈ U}
  let t : ι → Set Γ := fun U => ((U.1.toOpenSubgroup : Subgroup Γ) : Set Γ)
  have htc : ∀ i, IsClosed (t i) := fun i => i.1.toOpenSubgroup.isClosed
  have hempty : NΓᶜ ∩ ⋂ i, t i = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro x ⟨hx1, hx2⟩
    have hxPL : x ∈ PL l H := by
      unfold PL
      rw [Subgroup.mem_iInf]
      intro U
      rw [Subgroup.mem_iInf]
      intro hU
      exact Set.mem_iInter.mp hx2 ⟨U, hU⟩
    rw [h, Subgroup.mem_bot] at hxPL
    subst hxPL
    exact hx1 ⟨1, N.toOpenSubgroup.one_mem, rfl⟩
  obtain ⟨u, hu⟩ := hKc.elim_finite_subfamily_closed t htc hempty
  choose e he using fun (i : ι) => i.2 (g : Γ) g.2
  refine ⟨∑ i ∈ u, e i, ?_⟩
  have hin : ((g : Γ) ^ l ^ (∑ i ∈ u, e i)) ∈ ⋂ i ∈ u, t i := by
    simp only [Set.mem_iInter]
    intro i hi
    have hle : e i ≤ ∑ j ∈ u, e j := Finset.single_le_sum (fun _ _ => Nat.zero_le _) hi
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hle
    rw [hd, pow_add, pow_mul]
    exact Subgroup.pow_mem _ (he i) _
  have hnot : (g : Γ) ^ l ^ (∑ i ∈ u, e i) ∈ NΓ := by
    by_contra hc
    have : (g : Γ) ^ l ^ (∑ i ∈ u, e i) ∈ NΓᶜ ∩ ⋂ i ∈ u, t i := ⟨hc, hin⟩
    rw [hu] at this
    exact this
  obtain ⟨n, hn, hn2⟩ := hnot
  have : n = g ^ l ^ (∑ i ∈ u, e i) := by
    apply Subtype.ext
    rw [hn2]
    simp
  rw [← this]
  exact hn

open UpperTheory.V.AlgebraTools in
private theorem fg_of_open (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
    (H : Subgroup Γ) (hH : IsOpen (H : Set Γ)) (s : Set H) (hs : s.Finite) (h : TopGen s) :
    ∃ s : Finset Γ, (Subgroup.closure (s : Set Γ)).topologicalClosure = ⊤ := by
  classical
  haveI : Finite (Γ ⧸ H) := Subgroup.quotient_finite_of_isOpen H hH
  have hS : ((Subtype.val '' s) ∪ Set.range (Quotient.out : Γ ⧸ H → Γ)).Finite :=
    (hs.image _).union (Set.finite_range _)
  refine ⟨hS.toFinset, ?_⟩
  rw [Set.Finite.coe_toFinset]
  set S := (Subtype.val '' s) ∪ Set.range (Quotient.out : Γ ⧸ H → Γ) with hSdef
  set K := (Subgroup.closure S).topologicalClosure with hK
  have hKc : IsClosed (K : Set Γ) := Subgroup.isClosed_topologicalClosure _
  have himg : Subtype.val '' ((Subgroup.closure s : Subgroup H) : Set H) ⊆ (K : Set Γ) := by
    rintro _ ⟨z, hz, rfl⟩
    apply Subgroup.le_topologicalClosure
    have hz' : H.subtype z ∈ (Subgroup.closure s).map H.subtype := ⟨z, hz, rfl⟩
    rw [MonoidHom.map_closure] at hz'
    exact Subgroup.closure_mono (Set.subset_union_left) hz'
  have hHK : ∀ y ∈ H, y ∈ K := by
    intro y hy
    have hd : Dense ((Subgroup.closure s : Subgroup H) : Set H) := h
    have h1 := image_closure_subset_closure_image (f := (Subtype.val : H → Γ)) continuous_subtype_val
      ⟨⟨y, hy⟩, hd ⟨y, hy⟩, rfl⟩
    exact closure_minimal himg hKc h1
  rw [eq_top_iff]
  intro g _
  obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul H g
  have hr : (QuotientGroup.mk g : Γ ⧸ H).out ∈ K :=
    Subgroup.le_topologicalClosure _ (Subgroup.subset_closure (Set.mem_union_right _ ⟨_, rfl⟩))
  have hg : g = (QuotientGroup.mk g : Γ ⧸ H).out * (k : Γ)⁻¹ := by
    rw [hk]; group
  rw [hg]
  exact K.mul_mem hr (K.inv_mem (hHK _ k.2))

theorem UpperTheory.V.Pa.BC.phi0 :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0), T.ProL → PhiCond G0.G₀ l := by
  intro l _ L G0 T hT
  classical
  apply phi_fg G0.frame
  set HΓ : Subgroup G0.Γ := (T.H.toOpenSubgroup : Subgroup G0.Γ) with hHΓ
  have hHΓo : IsOpen (HΓ : Set G0.Γ) := T.H.toOpenSubgroup.isOpen
  have hHΓc : IsClosed (HΓ : Set G0.Γ) := T.H.toOpenSubgroup.isClosed
  haveI : CompactSpace HΓ := isCompact_iff_compactSpace.mp hHΓc.isCompact
  have hpro : UpperTheory.V.AlgebraTools.IsProL l HΓ := isProL_of_PL l G0.Γ HΓ hHΓo hT.1
  have hfin : {f : HΓ →* Multiplicative (ZMod l) | IsOpen (f.ker : Set HΓ)}.Finite :=
    Set.finite_coe_iff.mp T.fin0
  obtain ⟨x, hx⟩ := (UpperTheory.V.AlgebraTools.topGen_of_hom l HΓ hpro).2 _ hfin (Nat.lt_pow_self (Fact.out : l.Prime).one_lt).le
  exact fg_of_open G0.Γ HΓ hHΓo (Set.range x) (Set.finite_range _) hx
