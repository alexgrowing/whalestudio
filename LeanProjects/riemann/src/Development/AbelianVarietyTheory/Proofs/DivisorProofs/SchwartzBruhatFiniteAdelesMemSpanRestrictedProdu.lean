import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.SBSpan

variable {F : Type} [Field F] [NumberField F]

def intG (v : Pl F) : AddSubgroup (Fv F v) := (v.adicCompletionIntegers F).toSubring.toAddSubgroup

theorem isOpen_intG (v : Pl F) : IsOpen (intG v : Set (Fv F v)) := Valued.isOpen_integer _

theorem isCompact_intG (v : Pl F) : IsCompact (intG v : Set (Fv F v)) :=
  isCompact_iff_compactSpace.2 (GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F v)

def IsBox (B : ∀ v : Pl F, AddSubgroup (Fv F v)) : Prop :=
  (∀ v, IsOpen (B v : Set (Fv F v))) ∧ (∀ v, B v ≤ intG v) ∧ ∀ᶠ v in cofinite, B v = intG v

theorem exists_box_of_mem_nhds {N : Set (Af F)} (hN : N ∈ 𝓝 0) :
    ∃ B : ∀ v : Pl F, AddSubgroup (Fv F v), IsBox B ∧ ∀ α : Af F, (∀ v, evalV F v α ∈ B v) → α ∈ N := by
  classical
  have hc := (RestrictedProduct.isEmbedding_structureMap
    (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) (𝓕 := cofinite)).continuous
  have h := hc.tendsto (fun w => ⟨0, zero_mem (w.adicCompletionIntegers F)⟩) hN
  have h' := mem_map.1 h
  rw [nhds_pi, mem_pi'] at h'
  obtain ⟨I, t, ht, hI⟩ := h'
  have hW : ∀ v : Pl F, ∃ W : OpenAddSubgroup (Fv F v),
      ∀ x : (v.adicCompletionIntegers F : Set (v.adicCompletion F)), (x : Fv F v) ∈ W → x ∈ t v := by
    intro v
    obtain ⟨u, hu, hut⟩ := (mem_nhds_subtype _ _ _).1 (ht v)
    obtain ⟨W, hW⟩ := NonarchimedeanAddGroup.is_nonarchimedean u hu
    exact ⟨W, fun x hx => hut (hW hx)⟩
  choose W hWt using hW
  refine ⟨fun v => if v ∈ I then intG v ⊓ (W v : AddSubgroup (Fv F v)) else intG v, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro v
    dsimp only
    split_ifs
    · rw [AddSubgroup.coe_inf]
      exact (isOpen_intG v).inter (W v).isOpen
    · exact isOpen_intG v
  · intro v
    dsimp only
    split_ifs
    · exact inf_le_left
    · exact le_rfl
  · filter_upwards [I.finite_toSet.compl_mem_cofinite] with v hv
    simp only [Set.mem_compl_iff, Finset.mem_coe] at hv
    simp [hv]
  · intro α hα
    have hint : ∀ v, evalV F v α ∈ v.adicCompletionIntegers F := fun v => by
      have := hα v
      dsimp only at this
      split_ifs at this
      · exact this.1
      · exact this
    have hm : (fun v => (⟨evalV F v α, hint v⟩ : (v.adicCompletionIntegers F : Set (v.adicCompletion F)))) ∈
        Set.pi (I : Set (HeightOneSpectrum (𝓞 F))) t := by
      intro v hv
      apply hWt
      have := hα v
      simp only [if_pos (Finset.mem_coe.1 hv)] at this
      exact this.2
    exact hI hm

theorem IsBox.inf {ι : Type} [Finite ι] {B : ι → ∀ v : Pl F, AddSubgroup (Fv F v)} (hB : ∀ j, IsBox (B j)) :
    IsBox (fun v => intG v ⊓ ⨅ j, B j v) := by
  refine ⟨fun v => ?_, fun v => inf_le_left, ?_⟩
  · rw [AddSubgroup.coe_inf, AddSubgroup.coe_iInf]
    exact (isOpen_intG v).inter (isOpen_iInter_of_finite fun j => (hB j).1 v)
  · filter_upwards [Filter.eventually_all.2 fun j => (hB j).2.2] with v hv
    exact inf_eq_left.2 (le_iInf fun j => (hv j).ge)

theorem exists_box_pi {κ : Type} [Fintype κ] {N : Set (κ → Af F)} (hN : N ∈ 𝓝 0) :
    ∃ B : ∀ v : Pl F, AddSubgroup (Fv F v), IsBox B ∧ ∀ y : κ → Af F, (∀ i v, evalV F v (y i) ∈ B v) → y ∈ N := by
  rw [nhds_pi, mem_pi'] at hN
  obtain ⟨I, t, ht, hI⟩ := hN
  choose B hB hBN using fun i => exists_box_of_mem_nhds (ht i)
  refine ⟨fun v => intG v ⊓ ⨅ i, B i v, IsBox.inf hB, fun y hy => hI fun i _ => hBN i _ fun v => ?_⟩
  exact AddSubgroup.mem_iInf.1 (AddSubgroup.mem_inf.1 (hy i v)).2 i

theorem IsBox.isOpen {B : ∀ v : Pl F, AddSubgroup (Fv F v)} (hB : IsBox B) :
    IsOpen {α : Af F | ∀ v, evalV F v α ∈ B v} := by
  classical
  have hfin : {v | ¬ B v = intG v}.Finite := hB.2.2
  have e : {α : Af F | ∀ v, evalV F v α ∈ B v} =
      {α : Af F | ∀ v, α.1 v ∈ (v.adicCompletionIntegers F : Set (v.adicCompletion F))} ∩
        ⋂ v ∈ hfin.toFinset, (fun α : Af F => α v) ⁻¹' (B v : Set (Fv F v)) := by
    ext α
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage, Set.Finite.mem_toFinset]
    constructor
    · intro h
      exact ⟨fun v => hB.2.1 v (h v), fun v _ => h v⟩
    · rintro ⟨h1, h2⟩ v
      by_cases hv : B v = intG v
      · rw [hv]; exact h1 v
      · exact h2 v hv
  rw [e]
  exact (RestrictedProduct.isOpen_forall_mem (fun v => Valued.isOpen_integer _)).inter
    (isOpen_biInter_finset fun v _ => (hB.1 v).preimage (RestrictedProduct.continuous_eval v))

theorem exists_nhds_add_eq {X : Type} [TopologicalSpace X] [AddCommGroup X] [IsTopologicalAddGroup X] {g : X → ℂ}
    (hg : g ∈ SB X) : ∃ V ∈ 𝓝 (0 : X), ∀ y, ∀ z ∈ V, g (y + z) = g y := by
  classical
  obtain ⟨hlc, hcs⟩ := hg
  have hK : IsCompact (tsupport g) := hcs
  have hfin : (g '' tsupport g).Finite := by
    haveI := isCompact_iff_compactSpace.1 hK
    have := (hlc.comp_continuous (continuous_subtype_val (p := fun x => x ∈ tsupport g))).range_finite
    rwa [Set.range_comp, Subtype.range_coe] at this
  have hV : ∀ c : ℂ, ∃ V ∈ 𝓝 (0 : X), c ≠ 0 → ∀ y, g y = c → ∀ z ∈ V, g (y + z) = c := by
    intro c
    by_cases hc : c = 0
    · exact ⟨Set.univ, Filter.univ_mem, fun h => (h hc).elim⟩
    · have hsub : g ⁻¹' {c} ⊆ tsupport g := fun y hy => subset_tsupport g (by
        simp only [Set.mem_preimage, Set.mem_singleton_iff] at hy
        rw [Function.mem_support, hy]; exact hc)
      obtain ⟨V, hV, hKV⟩ := compact_open_separated_add_right
        (hK.of_isClosed_subset (hlc.isClosed_fiber c) hsub) (hlc.isOpen_fiber c) subset_rfl
      exact ⟨V, hV, fun _ y hy z hz => hKV (Set.add_mem_add hy hz)⟩
  choose V hV0 hVc using hV
  refine ⟨⋂ c ∈ hfin.toFinset, (V c ∩ -V c), (Filter.biInter_finset_mem _).2 fun c _ =>
    Filter.inter_mem (hV0 c) (neg_mem_nhds_zero X (hV0 c)), fun y z hz => ?_⟩
  have hz' : ∀ c ∈ g '' tsupport g, z ∈ V c ∧ -z ∈ V c := fun c hc => by
    have := Set.mem_iInter₂.1 hz c (hfin.mem_toFinset.2 hc)
    exact ⟨this.1, this.2⟩
  by_cases hy : g y = 0
  · by_contra hne
    have hne' : g (y + z) ≠ 0 := by rw [hy] at hne; exact hne
    have hmem : g (y + z) ∈ g '' tsupport g := ⟨y + z, subset_tsupport g hne', rfl⟩
    have := hVc (g (y + z)) hne' (y + z) rfl (-z) (hz' _ hmem).2
    rw [add_neg_cancel_right] at this
    exact hne this.symm
  · have hmem : g y ∈ g '' tsupport g := ⟨y, subset_tsupport g hy, rfl⟩
    exact hVc (g y) hy y rfl z (hz' _ hmem).1

theorem indicator_mem_SB {X : Type} [TopologicalSpace X] {C : Set X} (ho : IsOpen C) (hc : IsClosed C)
    (hk : IsCompact C) : Set.indicator C (1 : X → ℂ) ∈ SB X := by
  refine ⟨?_, HasCompactSupport.intro' hk hc fun y hy => Set.indicator_of_notMem hy _⟩
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  by_cases hx : x ∈ C
  · filter_upwards [ho.mem_nhds hx] with y hy
    rw [Set.indicator_of_mem hy, Set.indicator_of_mem hx]
    rfl
  · filter_upwards [hc.isOpen_compl.mem_nhds hx] with y hy
    rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]

def locInd (B : ∀ v : Pl F, AddSubgroup (Fv F v)) {κ : Type} (r : κ → Af F) (v : Pl F) : (κ → Fv F v) → ℂ :=
  Set.indicator {x | ∀ i, x i - evalV F v (r i) ∈ B v} 1

theorem locInd_mem_SB {B : ∀ v : Pl F, AddSubgroup (Fv F v)} (hB : IsBox B) {κ : Type} [Fintype κ]
    (r : κ → Af F) (v : Pl F) : locInd B r v ∈ SB (κ → Fv F v) := by
  have hBc : IsClosed (B v : Set (Fv F v)) := AddSubgroup.isClosed_of_isOpen _ (hB.1 v)
  have e : {x : κ → Fv F v | ∀ i, x i - evalV F v (r i) ∈ B v} =
      (fun x => x - fun i => evalV F v (r i)) ⁻¹' Set.pi Set.univ (fun _ => (B v : Set (Fv F v))) := by
    ext x
    simp
  have hcont : Continuous fun x : κ → Fv F v => x - fun i => evalV F v (r i) := continuous_id.sub continuous_const
  unfold locInd
  rw [e]
  refine indicator_mem_SB ((isOpen_set_pi Set.finite_univ fun _ _ => hB.1 v).preimage hcont)
    ((isClosed_set_pi fun _ _ => hBc).preimage hcont) ?_
  exact (Homeomorph.subRight fun i => evalV F v (r i)).isCompact_preimage.2
    (isCompact_univ_pi fun _ => (isCompact_intG v).of_isClosed_subset hBc (hB.2.1 v))

theorem locInd_eventually {B : ∀ v : Pl F, AddSubgroup (Fv F v)} (hB : IsBox B) {κ : Type} [Finite κ]
    (r : κ → Af F) : ∀ᶠ v in cofinite,
      locInd B r v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 := by
  filter_upwards [hB.2.2, Filter.eventually_all.2 fun i => (r i).2] with v hv hr
  unfold locInd
  congr 1
  ext x
  simp only [Set.mem_setOf_eq, hv]
  refine forall_congr' fun i => ⟨fun h => ?_, fun h => sub_mem (show x i ∈ intG v from h) (hr i)⟩
  have := add_mem h (show evalV F v (r i) ∈ intG v from hr i)
  rwa [sub_add_cancel] at this

open Classical in
theorem finprod_locInd {B : ∀ v : Pl F, AddSubgroup (Fv F v)} (hB : IsBox B) {κ : Type} [Finite κ]
    (r y : κ → Af F) : ∏ᶠ v, locInd B r v (fun i => evalV F v (y i)) =
      if ∀ i v, evalV F v (y i) - evalV F v (r i) ∈ B v then 1 else 0 := by
  classical
  have hone : ∀ᶠ v in cofinite, locInd B r v (fun i => evalV F v (y i)) = 1 := by
    filter_upwards [hB.2.2, Filter.eventually_all.2 fun i => (r i).2,
      Filter.eventually_all.2 fun i => (y i).2] with v hv hr hy
    apply Set.indicator_of_mem
    intro i
    rw [hv]
    exact sub_mem (hy i) (hr i)
  have hfin : Function.HasFiniteMulSupport fun v => locInd B r v (fun i => evalV F v (y i)) :=
    Filter.eventually_cofinite.1 hone
  split_ifs with h
  · exact finprod_eq_one_of_forall_eq_one fun v => Set.indicator_of_mem
      (show (fun i => evalV F v (y i)) ∈ {x : κ → Fv F v | ∀ i, x i - evalV F v (r i) ∈ B v} from fun i => h i v) _
  · push_neg at h
    obtain ⟨i, v, hv⟩ := h
    exact finprod_eq_zero _ v (Set.indicator_of_notMem
      (show (fun i => evalV F v (y i)) ∉ {x : κ → Fv F v | ∀ i, x i - evalV F v (r i) ∈ B v} from
        fun hx => hv (hx i)) _) hfin

theorem mem_span_restrictedProd : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ], ∀ g ∈ SB (κ → Af F),
    g ∈ Submodule.span ℂ {p : (κ → Af F) → ℂ | ∃ φ : ∀ v : Pl F, (κ → Fv F v) → ℂ, (∀ v, φ v ∈ SB (κ → Fv F v)) ∧
      (∀ᶠ v in cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) ∧
      p = fun y => ∏ᶠ v, φ v fun i => evalV F v (y i)} := by
  intro F _ _ κ _ g hg
  classical
  obtain ⟨V, hV, hVg⟩ := exists_nhds_add_eq hg
  obtain ⟨B, hB, hBV⟩ := exists_box_pi hV
  let U : AddSubgroup (κ → Af F) :=
    { carrier := {y | ∀ i v, evalV F v (y i) ∈ B v}
      add_mem' := fun ha hb i v => by simpa only [Pi.add_apply, map_add] using add_mem (ha i v) (hb i v)
      zero_mem' := fun i v => by simpa only [Pi.zero_apply, map_zero] using zero_mem (B v)
      neg_mem' := fun ha i v => by simpa only [Pi.neg_apply, map_neg] using neg_mem (ha i v) }
  have hmemU : ∀ y, y ∈ U ↔ ∀ i v, evalV F v (y i) ∈ B v := fun y => Iff.rfl
  have hUo : IsOpen (U : Set (κ → Af F)) := by
    have : (U : Set (κ → Af F)) = ⋂ i, (fun y : κ → Af F => y i) ⁻¹' {α : Af F | ∀ v, evalV F v α ∈ B v} := by
      ext y
      simp only [SetLike.mem_coe, hmemU, Set.mem_iInter, Set.mem_preimage, Set.mem_setOf_eq]
    rw [this]
    exact isOpen_iInter_of_finite fun i => hB.isOpen.preimage (continuous_apply i)
  have hinv : ∀ y, ∀ u ∈ U, g (y + u) = g y := fun y u hu => hVg y u (hBV u hu)
  haveI := QuotientAddGroup.discreteTopology hUo
  have hK : IsCompact (tsupport g) := hg.2
  have hQ : ((QuotientAddGroup.mk : (κ → Af F) → (κ → Af F) ⧸ U) '' tsupport g).Finite :=
    (show IsCompact ((QuotientAddGroup.mk : (κ → Af F) → (κ → Af F) ⧸ U) '' tsupport g) from
      hK.image continuous_quot_mk).finite_of_discrete
  have key : g = ∑ q ∈ hQ.toFinset, g q.out • fun y => ∏ᶠ v, locInd B q.out v fun i => evalV F v (y i) := by
    funext y
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, finprod_locInd hB]
    have hc : ∀ q : (κ → Af F) ⧸ U, (∀ i v, evalV F v (y i) - evalV F v (q.out i) ∈ B v) ↔
        (QuotientAddGroup.mk y : (κ → Af F) ⧸ U) = q := by
      intro q
      conv_rhs => rw [← QuotientAddGroup.out_eq' q]
      rw [QuotientAddGroup.eq, ← U.neg_mem_iff, neg_add_rev, neg_neg, neg_add_eq_sub, hmemU]
      simp only [Pi.sub_apply, map_sub]
    simp only [hc, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq]
    split_ifs with h
    · have h1 := QuotientAddGroup.eq.1 (QuotientAddGroup.out_eq' (QuotientAddGroup.mk y : (κ → Af F) ⧸ U))
      rw [neg_add_eq_sub] at h1
      have := hinv (QuotientAddGroup.mk y : (κ → Af F) ⧸ U).out _ h1
      rwa [add_sub_cancel] at this
    · refine image_eq_zero_of_notMem_tsupport fun hy => h ?_
      exact hQ.mem_toFinset.2 ⟨y, hy, rfl⟩
  rw [key]
  refine Submodule.sum_mem _ fun q _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  exact ⟨locInd B q.out, fun v => locInd_mem_SB hB _ v, locInd_eventually hB _, rfl⟩

end GlobalTheory.SBSpan

end
