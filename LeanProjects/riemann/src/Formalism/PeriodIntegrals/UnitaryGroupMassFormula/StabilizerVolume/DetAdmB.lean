import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.DetAdmA

noncomputable section

namespace PI.VolStabS.DeterminantAdmissible

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain MeasureTheory Topology Filter Set
  MeasurableSpace
open scoped TensorProduct ENNReal RestrictedProduct

section Boxes

variable {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι]

def boxS (D : ι → ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)) : Set (ι → Af F) :=
  {y | ∀ c v, y c v ∈ D c v}

def IsBoxD (D : ι → ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)) : Prop :=
  (∀ c v, IsClopen (D c v) ∧ IsCompact (D c v)) ∧
    ∀ᶠ v in cofinite, ∀ c, D c v = (v.adicCompletionIntegers F : Set (Fv F v))

variable (F ι) in

def boxes : Set (Set (ι → Af F)) := {s | ∃ D, IsBoxD D ∧ s = boxS D}

theorem boxS_eq (D : ι → ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)) :
    boxS D = Set.pi univ fun c => {x : Af F | ∀ v, x v ∈ D c v} := by
  ext y
  simp [boxS]

private theorem isOpen_isCompact_restrictedProduct_box {κ : Type*} {R : κ → Type*} [∀ i, TopologicalSpace (R i)]
    {A : ∀ i, Set (R i)} (hA : ∀ i, IsOpen (A i)) (D : ∀ i, Set (R i))
    (hDo : ∀ i, IsOpen (D i)) (hDc : ∀ i, IsCompact (D i))
    (hcof : ∀ᶠ i in cofinite, D i = A i) :
    IsOpen {f : Πʳ i, [R i, A i] | ∀ i, f i ∈ D i} ∧
      IsCompact {f : Πʳ i, [R i, A i] | ∀ i, f i ∈ D i} := by
  set S : Set κ := {i | D i = A i} with hSdef
  have hS : cofinite ≤ 𝓟 S := le_principal_iff.2 hcof
  have hfin : Sᶜ.Finite := mem_cofinite.1 hcof
  have himg : {f : Πʳ i, [R i, A i] | ∀ i, f i ∈ D i} =
      RestrictedProduct.inclusion R A hS ''
        (((↑) : Πʳ i, [R i, A i]_[𝓟 S] → Π i, R i) ⁻¹' (univ.pi D)) := by
    ext f
    constructor
    · intro hf
      refine ⟨⟨fun i => f i, ?_⟩, ?_, ?_⟩
      · exact eventually_principal.2 fun i hi => by
          have h : D i = A i := hi
          show f i ∈ A i
          rw [← h]
          exact hf i
      · intro i _
        exact hf i
      · rfl
    · rintro ⟨g, hg, rfl⟩ i
      exact hg i (mem_univ i)
  rw [himg]
  constructor
  · refine (RestrictedProduct.isOpenEmbedding_inclusion_principal hA hS).isOpenMap _ ?_
    have h : (((↑) : Πʳ i, [R i, A i]_[𝓟 S] → Π i, R i) ⁻¹' (univ.pi D)) =
        ((↑) : Πʳ i, [R i, A i]_[𝓟 S] → Π i, R i) ⁻¹' (Sᶜ.pi D) := by
      ext g
      simp only [mem_preimage, Set.mem_pi]
      refine ⟨fun h i _ => h i (mem_univ i), fun h i _ => ?_⟩
      by_cases hi : i ∈ S
      · have h' : D i = A i := hi
        rw [h']
        exact g.2 hi
      · exact h i hi
    rw [h]
    exact (isOpen_set_pi hfin fun i _ => hDo i).preimage RestrictedProduct.continuous_coe
  · refine IsCompact.image ?_ (RestrictedProduct.continuous_inclusion hS)
    refine (RestrictedProduct.isEmbedding_coe_of_principal.isCompact_preimage_iff ?_).2
      (isCompact_univ_pi hDc)
    rw [RestrictedProduct.range_coe_principal]
    intro g hg i hi
    have h : D i = A i := hi
    rw [← h]
    exact hg i (mem_univ i)

theorem isCompact_boxS {D : ι → ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)} (hD : IsBoxD D) :
    IsCompact (boxS D) := by
  rw [boxS_eq]
  exact isCompact_univ_pi fun c => (isOpen_isCompact_restrictedProduct_box (fun v => Valued.isOpen_valuationSubring _)
    (D c) (fun v => (hD.1 c v).1.isOpen) (fun v => (hD.1 c v).2) (hD.2.mono fun v h => h c)).2

theorem isOpen_boxS {D : ι → ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)} (hD : IsBoxD D) :
    IsOpen (boxS D) := by
  rw [boxS_eq]
  exact isOpen_set_pi finite_univ fun c _ => (isOpen_isCompact_restrictedProduct_box
    (fun v => Valued.isOpen_valuationSubring _) (D c) (fun v => (hD.1 c v).1.isOpen)
    (fun v => (hD.1 c v).2) (hD.2.mono fun v h => h c)).1

theorem boxes_inter {s t : Set (ι → Af F)} (hs : s ∈ boxes F ι) (ht : t ∈ boxes F ι) :
    s ∩ t ∈ boxes F ι := by
  obtain ⟨D, hD, rfl⟩ := hs
  obtain ⟨D', hD', rfl⟩ := ht
  refine ⟨fun c v => D c v ∩ D' c v, ⟨fun c v => ⟨(hD.1 c v).1.inter (hD'.1 c v).1,
    (hD.1 c v).2.inter_right (hD'.1 c v).1.isClosed⟩, ?_⟩, ?_⟩
  · filter_upwards [hD.2, hD'.2] with v h1 h2 c
    rw [h1 c, h2 c, inter_self]
  · ext y
    simp only [boxS, mem_inter_iff, mem_ofPred_eq]
    constructor
    · rintro ⟨h1, h2⟩ c v
      exact ⟨h1 c v, h2 c v⟩
    · intro h
      exact ⟨fun c v => (h c v).1, fun c v => (h c v).2⟩

private theorem preimage_sub_integers_mem_and_eq_of_mem (v : HeightOneSpectrum (𝓞 F)) (a : Fv F v) :
    IsClopen ((fun z => z - a) ⁻¹' (v.adicCompletionIntegers F : Set (Fv F v))) ∧
      IsCompact ((fun z => z - a) ⁻¹' (v.adicCompletionIntegers F : Set (Fv F v))) ∧
      a ∈ (fun z => z - a) ⁻¹' (v.adicCompletionIntegers F : Set (Fv F v)) ∧
      (a ∈ v.adicCompletionIntegers F →
        (fun z => z - a) ⁻¹' (v.adicCompletionIntegers F : Set (Fv F v)) =
          (v.adicCompletionIntegers F : Set (Fv F v))) := by
  have hOc := AdicCompletionValuation.isCompact_adicCompletionIntegers F v
  have hOo : IsOpen (v.adicCompletionIntegers F : Set (Fv F v)) := Valued.isOpen_valuationSubring _
  refine ⟨IsClopen.preimage ⟨hOc.isClosed, hOo⟩ (continuous_id.sub continuous_const),
    (Homeomorph.subRight a).isCompact_preimage.2 hOc, ?_, fun ha => ?_⟩
  · simp only [mem_preimage, sub_self, SetLike.mem_coe]
    exact zero_mem _
  · ext z
    simp only [mem_preimage, SetLike.mem_coe]
    constructor
    · intro h
      simpa using add_mem h ha
    · intro h
      exact sub_mem h ha

theorem exists_box_mem (y : ι → Af F) : ∃ D, IsBoxD D ∧ y ∈ boxS D := by
  refine ⟨fun c v => (fun z => z - y c v) ⁻¹' (v.adicCompletionIntegers F : Set (Fv F v)),
    ⟨fun c v => ⟨(preimage_sub_integers_mem_and_eq_of_mem v (y c v)).1, (preimage_sub_integers_mem_and_eq_of_mem v (y c v)).2.1⟩, ?_⟩, ?_⟩
  · filter_upwards [eventually_all.2 fun c => (y c).2] with v hv c
    exact (preimage_sub_integers_mem_and_eq_of_mem v (y c v)).2.2.2 (hv c)
  · show ∀ c v, y c v ∈ (fun z => z - y c v) ⁻¹' (v.adicCompletionIntegers F : Set (Fv F v))
    exact fun c v => (preimage_sub_integers_mem_and_eq_of_mem v (y c v)).2.2.1

theorem boxes_seq : ∃ bs : ℕ → Set (ι → Af F), (∀ n, bs n ∈ boxes F ι) ∧ ⋃ n, bs n = univ := by
  have hopen : ∀ s ∈ boxes F ι, IsOpen s := by
    rintro s ⟨D, hD, rfl⟩
    exact isOpen_boxS hD
  obtain ⟨T, hTc, hTS, hTU⟩ := TopologicalSpace.isOpen_sUnion_countable (boxes F ι) hopen
  have hU : ⋃₀ boxes F ι = univ := by
    refine eq_univ_of_forall fun y => ?_
    obtain ⟨D, hD, hy⟩ := exists_box_mem y
    exact ⟨boxS D, ⟨D, hD, rfl⟩, hy⟩
  have hTne : T.Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty] at h
    rw [h, sUnion_empty, hU] at hTU
    exact empty_ne_univ hTU
  obtain ⟨bs, rfl⟩ := hTc.exists_eq_range hTne
  refine ⟨bs, fun n => hTS (mem_range_self n), ?_⟩
  rw [← sUnion_range, hTU, hU]

theorem isCountablySpanning_boxes : IsCountablySpanning (boxes F ι) := by
  obtain ⟨bs, h1, h2⟩ := boxes_seq (F := F) (ι := ι)
  exact ⟨bs, h1, h2⟩

open Classical in

def upd (D : ι → ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)) (c : ι)
    (v : HeightOneSpectrum (𝓞 F)) (C : Set (Fv F v)) : ι → ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v) :=
  fun c' => if c' = c then Function.update (D c) v (D c v ∩ C) else D c'

private theorem exists_restricted_box_subset_of_isOpen {x : Af F} {U : Set (Af F)} (hU : IsOpen U) (hx : x ∈ U) :
    ∃ E : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v),
      (∀ v, IsClopen (E v) ∧ IsCompact (E v)) ∧
      (∀ᶠ v in cofinite, E v = (v.adicCompletionIntegers F : Set (Fv F v))) ∧
      (∀ v, x v ∈ E v) ∧ {z : Af F | ∀ v, z v ∈ E v} ⊆ U := by
  classical
  have hA : ∀ v : HeightOneSpectrum (𝓞 F),
      IsOpen (v.adicCompletionIntegers F : Set (Fv F v)) :=
    fun v => Valued.isOpen_valuationSubring _
  set S : Set (HeightOneSpectrum (𝓞 F)) := {v | x v ∈ v.adicCompletionIntegers F} with hSdef
  have hSc : S ∈ cofinite := x.2
  have hS : cofinite ≤ 𝓟 S := le_principal_iff.2 hSc
  let x' : Πʳ v : HeightOneSpectrum (𝓞 F),
      [Fv F v, (v.adicCompletionIntegers F : Set (Fv F v))]_[𝓟 S] :=
    ⟨fun v => x v, eventually_principal.2 fun v hv => hv⟩
  have hUx : U ∈ 𝓝 (RestrictedProduct.inclusion _ _ hS x') := hU.mem_nhds hx
  rw [RestrictedProduct.nhds_eq_map_inclusion hA hS] at hUx
  have hUx2 : (RestrictedProduct.inclusion _ _ hS) ⁻¹' U ∈ 𝓝 x' := hUx
  rw [RestrictedProduct.isEmbedding_coe_of_principal.nhds_eq_comap, mem_comap] at hUx2
  obtain ⟨N, hN, hNU⟩ := hUx2
  rw [nhds_pi, Filter.mem_pi] at hN
  obtain ⟨I, hI, t, ht, hIt⟩ := hN
  have key : ∀ v, ∃ V : Set (Fv F v), IsClopen V ∧ x v ∈ V ∧
      V ⊆ t v ∩ (fun z => z - x v) ⁻¹' (v.adicCompletionIntegers F : Set (Fv F v)) := by
    intro v
    obtain ⟨hT1, -, hT3, -⟩ := preimage_sub_integers_mem_and_eq_of_mem v (x v)
    obtain ⟨W, hWt, hWo, hxW⟩ := mem_nhds_iff.1 (ht v)
    obtain ⟨V, hV, hxV, hVW⟩ :=
      (loc_compact_Haus_tot_disc_of_zero_dim (H := Fv F v)).exists_subset_of_mem_open
        (show x v ∈ W ∩ _ from ⟨hxW, hT3⟩) (hWo.inter hT1.isOpen)
    exact ⟨V, hV, hxV, hVW.trans (inter_subset_inter_left _ hWt)⟩
  choose V hVc hxV hVsub using key
  obtain ⟨E, hEv⟩ : ∃ E : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v), ∀ v, E v =
      if v ∈ I then V v
      else (fun z => z - x v) ⁻¹' (v.adicCompletionIntegers F : Set (Fv F v)) :=
    ⟨_, fun v => rfl⟩
  have hEsub : ∀ v, E v ⊆ (fun z => z - x v) ⁻¹' (v.adicCompletionIntegers F : Set (Fv F v)) := by
    intro v
    by_cases hv : v ∈ I
    · rw [hEv v, if_pos hv]
      exact (hVsub v).trans inter_subset_right
    · rw [hEv v, if_neg hv]
  refine ⟨E, fun v => ?_, ?_, fun v => ?_, ?_⟩
  · obtain ⟨hT1, hT2, -, -⟩ := preimage_sub_integers_mem_and_eq_of_mem v (x v)
    by_cases hv : v ∈ I
    · rw [hEv v, if_pos hv]
      exact ⟨hVc v, hT2.of_isClosed_subset (hVc v).1 ((hVsub v).trans inter_subset_right)⟩
    · rw [hEv v, if_neg hv]
      exact ⟨hT1, hT2⟩
  · filter_upwards [hSc, hI.compl_mem_cofinite] with v hvS hvI
    rw [hEv v, if_neg hvI]
    exact (preimage_sub_integers_mem_and_eq_of_mem v (x v)).2.2.2 hvS
  · by_cases hv : v ∈ I
    · rw [hEv v, if_pos hv]
      exact hxV v
    · rw [hEv v, if_neg hv]
      exact (preimage_sub_integers_mem_and_eq_of_mem v (x v)).2.2.1
  · intro z hz
    have hz1 : ∀ v, z v ∈ E v := hz
    have hzE : ∀ v, z v - x v ∈ v.adicCompletionIntegers F := fun v => hEsub v (hz1 v)
    let z' : Πʳ v : HeightOneSpectrum (𝓞 F),
        [Fv F v, (v.adicCompletionIntegers F : Set (Fv F v))]_[𝓟 S] :=
      ⟨fun v => z v, eventually_principal.2 fun v hv => by
        have h2 : x v ∈ v.adicCompletionIntegers F := hv
        simpa using add_mem (hzE v) h2⟩
    have hz' : z' ∈ ((↑) : _ → Π v, Fv F v) ⁻¹' N := hIt fun v hv => by
      have h := hz1 v
      rw [hEv v, if_pos hv] at h
      exact ((hVsub v) h).1
    exact hNU hz'

theorem generateFrom_boxes : generateFrom (boxes F ι) = (MeasurableSpace.pi : MeasurableSpace (ι → Af F)) := by
  refine le_antisymm (generateFrom_le ?_) ?_
  · rintro s ⟨D, hD, rfl⟩
    exact (isOpen_boxS hD).measurableSet
  · have hb : (MeasurableSpace.pi : MeasurableSpace (ι → Af F)) = borel (ι → Af F) :=
      BorelSpace.measurable_eq
    rw [hb, borel]
    refine generateFrom_le fun O hO => ?_
    have hO' : IsOpen O := hO
    set Bs : Set (Set (ι → Af F)) := {s | s ∈ boxes F ι ∧ s ⊆ O} with hBs
    obtain ⟨T, hTc, hTB, hTU⟩ := TopologicalSpace.isOpen_sUnion_countable Bs (fun s hs => by
      obtain ⟨D, hD, hsD⟩ := hs.1
      rw [hsD]
      exact isOpen_boxS hD)
    have hOU : ⋃₀ Bs = O := by
      refine Subset.antisymm (sUnion_subset fun s hs => hs.2) fun y hy => ?_
      have hN : O ∈ 𝓝 y := hO'.mem_nhds hy
      rw [nhds_pi, Filter.mem_pi] at hN
      obtain ⟨I, -, t, ht, hIt⟩ := hN
      have hE : ∀ c, ∃ E : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v),
          (∀ v, IsClopen (E v) ∧ IsCompact (E v)) ∧
          (∀ᶠ v in cofinite, E v = (v.adicCompletionIntegers F : Set (Fv F v))) ∧
          (∀ v, y c v ∈ E v) ∧ {z : Af F | ∀ v, z v ∈ E v} ⊆ t c := fun c => by
        obtain ⟨U, hUt, hUo, hyU⟩ := mem_nhds_iff.1 (ht c)
        obtain ⟨E, h1, h2, h3, h4⟩ := exists_restricted_box_subset_of_isOpen hUo hyU
        exact ⟨E, h1, h2, h3, h4.trans hUt⟩
      choose E hE1 hE2 hE3 hE4 using hE
      have hyE : y ∈ boxS E := by
        show ∀ c v, y c v ∈ E c v
        exact fun c v => hE3 c v
      refine ⟨boxS E, ⟨⟨E, ⟨hE1, eventually_all.2 hE2⟩, rfl⟩, fun z hz => hIt fun c _ => ?_⟩, hyE⟩
      have hz' : ∀ c v, z c v ∈ E c v := hz
      exact hE4 c (hz' c)
    rw [← hOU, ← hTU]
    exact MeasurableSet.sUnion hTc fun s hs => measurableSet_generateFrom (hTB hs).1

end Boxes

end PI.VolStabS.DeterminantAdmissible
