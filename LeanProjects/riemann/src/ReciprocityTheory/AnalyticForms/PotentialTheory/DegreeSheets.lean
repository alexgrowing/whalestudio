import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialPullbackStatement
import ReciprocityTheory.AnalyticForms.PotentialTheory.Pullback
import ReciprocityTheory.AnalyticForms.PotentialTheory.AnalyticSubsetChartLocal
import ReciprocityTheory.AnalyticForms.PotentialTheory.IntegrableOnTargetOfTsupport
import ReciprocityTheory.AnalyticForms.PotentialTheory.Partition
import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffAtOfIsPotential

namespace ReciprocityTheory.AnForm.M

open FinHolAtlas Topology

noncomputable section

variable {e : ℕ} {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

theorem isClosed_of_isAnalyticSubset' (A : FinHolAtlas e X) {S : Set X}
    (hS : A.IsAnalyticSubset S) : IsClosed S := by
  unfold FinHolAtlas.IsAnalyticSubset at hS
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro x hx
  obtain ⟨W, hW, hxW, r, f, hf, hSW⟩ := hS x
  have hne : ∃ i, f i x ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    apply hx
    have hxSW : x ∈ S ∩ W := by
      rw [hSW]
      exact ⟨hxW, hcon⟩
    exact hxSW.1
  obtain ⟨i, hi⟩ := hne
  have hca : ContinuousAt (f i) x := by
    obtain ⟨j, hxj⟩ := A.cover x
    have h : ∀ k, AnalyticOnNhd ℂ ((f i) ∘ (A.chart k).symm)
        ((A.chart k).target ∩ (A.chart k).symm ⁻¹' W) := hf i
    have hmem : (A.chart j) x ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' W := by
      refine ⟨(A.chart j).map_source hxj, ?_⟩
      show (A.chart j).symm ((A.chart j) x) ∈ W
      rw [(A.chart j).left_inv hxj]
      exact hxW
    have h1 : ContinuousAt ((f i ∘ (A.chart j).symm) ∘ (A.chart j)) x :=
      ((h j _ hmem).continuousAt).comp ((A.chart j).continuousAt hxj)
    refine h1.congr ?_
    filter_upwards [(A.chart j).open_source.mem_nhds hxj] with y hy
    simp only [Function.comp_apply, (A.chart j).left_inv hy]
  filter_upwards [hW.mem_nhds hxW, hca.eventually_ne hi] with y hyW hyi hyS
  have hy : y ∈ S ∩ W := ⟨hyS, hyW⟩
  rw [hSW] at hy
  exact hyi (hy.2 i)

theorem exists_localHomeomorph_of_isDegreeOff {A : FinHolAtlas e X} {B : FinHolAtlas e Y}
    {h : Y → X} (hh : HoloMap B A h) {d : ℕ} {S : Set X} (hd : IsDegreeOff A B h d S) (y : Y)
    (hy : h y ∉ S) :
    ∃ E : OpenPartialHomeomorph Y X, y ∈ E.source ∧ Set.EqOn h E E.source ∧
      ∃ j : Fin B.n, E.source ⊆ (B.chart j).source := by
  obtain ⟨j, hyj⟩ := B.cover y
  obtain ⟨k, hk⟩ := A.cover (h y)
  have hb : (B.chart j) y ∈ (B.chart j).target ∩ (B.chart j).symm ⁻¹' (h ⁻¹' (A.chart k).source) := by
    refine ⟨(B.chart j).map_source hyj, ?_⟩
    show h ((B.chart j).symm ((B.chart j) y)) ∈ (A.chart k).source
    rw [(B.chart j).left_inv hyj]
    exact hk
  have han := hh.2 j k ((B.chart j) y) hb
  have hdet := hd.2.2.2.2.2 j k ((B.chart j) y) ((B.chart j).map_source hyj)
    (by rw [(B.chart j).left_inv hyj]; exact hy) (by rw [(B.chart j).left_inv hyj]; exact hk)
  set L := (LinearMap.equivOfDetNeZero _ hdet).toContinuousLinearEquiv with hL
  have hstrict : HasStrictFDerivAt ((A.chart k) ∘ h ∘ (B.chart j).symm)
      (L : (Fin e → ℂ) →L[ℂ] (Fin e → ℂ)) ((B.chart j) y) :=
    han.hasStrictFDerivAt.congr_fderiv (by ext v; rfl)
  set Φ := hstrict.toOpenPartialHomeomorph ((A.chart k) ∘ h ∘ (B.chart j).symm) with hΦ
  have hcoe : (Φ : (Fin e → ℂ) → (Fin e → ℂ)) = (A.chart k) ∘ h ∘ (B.chart j).symm :=
    hstrict.toOpenPartialHomeomorph_coe
  have hsrc : (B.chart j) y ∈ Φ.source := hstrict.mem_toOpenPartialHomeomorph_source
  have hU : IsOpen (h ⁻¹' (A.chart k).source) := (A.chart k).open_source.preimage hh.1
  refine ⟨(((B.chart j).trans Φ).trans (A.chart k).symm).restrOpen _ hU, ?_, ?_, j, ?_⟩
  · rw [OpenPartialHomeomorph.restrOpen_source, OpenPartialHomeomorph.trans_source,
      OpenPartialHomeomorph.trans_source]
    refine ⟨⟨⟨hyj, hsrc⟩, ?_⟩, hk⟩
    show Φ ((B.chart j) y) ∈ (A.chart k).target
    rw [hcoe]
    show (A.chart k) (h ((B.chart j).symm ((B.chart j) y))) ∈ (A.chart k).target
    rw [(B.chart j).left_inv hyj]
    exact (A.chart k).map_source hk
  · intro y' hy'
    rw [OpenPartialHomeomorph.restrOpen_source, OpenPartialHomeomorph.trans_source,
      OpenPartialHomeomorph.trans_source] at hy'
    obtain ⟨⟨⟨hy1, -⟩, -⟩, hy4⟩ := hy'
    show h y' = (A.chart k).symm (Φ ((B.chart j) y'))
    rw [hcoe]
    show h y' = (A.chart k).symm ((A.chart k) (h ((B.chart j).symm ((B.chart j) y'))))
    rw [(B.chart j).left_inv hy1, (A.chart k).left_inv hy4]
  · intro y' hy'
    rw [OpenPartialHomeomorph.restrOpen_source, OpenPartialHomeomorph.trans_source,
      OpenPartialHomeomorph.trans_source] at hy'
    exact hy'.1.1.1

theorem degree_local_sheets' [CompactSpace Y] [T2Space Y] [T2Space X]
    {A : FinHolAtlas e X} {B : FinHolAtlas e Y} {h : Y → X} (hh : HoloMap B A h) {d : ℕ}
    {S : Set X} (hd : IsDegreeOff A B h d S) (x : X) (hx : x ∉ S) :
    ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ Disjoint V S ∧ ∃ k : Fin A.n, V ⊆ (A.chart k).source ∧
      ∃ W : Fin d → Set Y, (∀ i, IsOpen (W i)) ∧ Pairwise (Function.onFun Disjoint W) ∧
        h ⁻¹' V = ⋃ i, W i ∧ ∀ i, Set.BijOn h (W i) V ∧
          ∃ j : Fin B.n, W i ⊆ (B.chart j).source := by
  classical
  have hSc : IsClosed S := isClosed_of_isAnalyticSubset' A hd.1
  have hloc : ∀ y : (h ⁻¹' {x} : Set Y), ∃ E : OpenPartialHomeomorph Y X, y.1 ∈ E.source ∧
      Set.EqOn h E E.source ∧ ∃ j : Fin B.n, E.source ⊆ (B.chart j).source := fun y =>
    exists_localHomeomorph_of_isDegreeOff hh hd y.1
      (by rw [show h y.1 = x from y.2]; exact hx)
  choose E hEy hEeq jE hjE using hloc
  have hFc : IsCompact (h ⁻¹' {x}) := (isClosed_singleton.preimage hh.1).isCompact
  have hFfin : (h ⁻¹' {x}).Finite := by
    obtain ⟨t, ht⟩ := hFc.elim_finite_subcover (fun y => (E y).source)
      (fun y => (E y).open_source) (fun y hy => Set.mem_iUnion.2 ⟨⟨y, hy⟩, hEy ⟨y, hy⟩⟩)
    refine (t.finite_toSet.image Subtype.val).subset ?_
    intro z hz
    obtain ⟨w, hwt, hzw⟩ := Set.mem_iUnion₂.1 (ht hz)
    have hzx : h z = x := hz
    have hwx : h w.1 = x := w.2
    have h1 : E w w.1 = E w z := by
      rw [← hEeq w hzw, ← hEeq w (hEy w), hzx, hwx]
    exact ⟨w, hwt, (E w).injOn (hEy w) hzw h1⟩
  have : Finite (h ⁻¹' {x}) := hFfin.to_subtype
  have hcard : Nat.card (h ⁻¹' {x}) = d := by
    rw [Nat.card_coe_set_eq]; exact hd.2.2.2.2.1 x hx
  let en : Fin d ≃ (h ⁻¹' {x} : Set Y) := ((Finite.equivFin _).trans (finCongr hcard)).symm
  obtain ⟨U0, hU0, hU0d⟩ := hFfin.t2_separation
  let U : Fin d → Set Y := fun i => U0 (en i).1 ∩ (E (en i)).source
  have hUo : ∀ i, IsOpen (U i) := fun i => (hU0 _).2.inter (E _).open_source
  have hyU : ∀ i, (en i).1 ∈ U i := fun i => ⟨(hU0 _).1, hEy _⟩
  have hUd : Pairwise (Function.onFun Disjoint U) := by
    intro i i' hii'
    have hne : (en i).1 ≠ (en i').1 := fun h' => hii' (en.injective (Subtype.ext h'))
    exact (hU0d (en i).2 (en i').2 hne).mono Set.inter_subset_left Set.inter_subset_left
  have hhU : ∀ i, h '' U i = E (en i) '' U i := fun i =>
    ((hEeq (en i)).mono Set.inter_subset_right).image_eq
  have hhUo : ∀ i, IsOpen (h '' U i) := fun i => by
    rw [hhU]; exact (E _).isOpen_image_of_subset_source (hUo i) Set.inter_subset_right
  have hKc : IsCompact (⋃ i, U i)ᶜ := (isOpen_iUnion hUo).isClosed_compl.isCompact
  have hK : IsClosed (h '' (⋃ i, U i)ᶜ) := (hKc.image hh.1).isClosed
  have hxK : x ∉ h '' (⋃ i, U i)ᶜ := by
    rintro ⟨z, hzK, hzx⟩
    apply hzK
    have hz : z ∈ h ⁻¹' {x} := hzx
    refine Set.mem_iUnion.2 ⟨en.symm ⟨z, hz⟩, ?_⟩
    have := hyU (en.symm ⟨z, hz⟩)
    simpa using this
  obtain ⟨k, hk⟩ := A.cover x
  let V : Set X := (⋂ i, h '' U i) ∩ (A.chart k).source ∩ (h '' (⋃ i, U i)ᶜ)ᶜ ∩ Sᶜ
  have hVo : IsOpen V :=
    (((isOpen_iInter_of_finite hhUo).inter (A.chart k).open_source).inter
      hK.isOpen_compl).inter hSc.isOpen_compl
  have hVU : ∀ i, V ⊆ h '' U i := fun i z hz => Set.mem_iInter.1 hz.1.1.1 i
  refine ⟨V, hVo, ⟨⟨⟨Set.mem_iInter.2 fun i => ⟨(en i).1, hyU i, (en i).2⟩, hk⟩, hxK⟩, hx⟩,
    Set.disjoint_left.2 fun z hz hzS => hz.2 hzS, k, fun z hz => hz.1.1.2, ?_⟩
  refine ⟨fun i => U i ∩ h ⁻¹' V, fun i => (hUo i).inter (hVo.preimage hh.1), ?_, ?_, ?_⟩
  · intro i i' hii'
    exact (hUd hii').mono Set.inter_subset_left Set.inter_subset_left
  · ext z
    constructor
    · intro hz
      have hzU : z ∈ ⋃ i, U i := by
        by_contra hc
        exact hz.1.2 ⟨z, hc, rfl⟩
      obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hzU
      exact Set.mem_iUnion.2 ⟨i, hi, hz⟩
    · intro hz
      obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hz
      exact hi.2
  · intro i
    refine ⟨⟨fun z hz => hz.2, ?_, ?_⟩, jE (en i), fun z hz => hjE _ hz.1.2⟩
    · intro a ha b hb hab
      apply (E (en i)).injOn ha.1.2 hb.1.2
      rw [← hEeq (en i) ha.1.2, ← hEeq (en i) hb.1.2]
      exact hab
    · intro v hv
      obtain ⟨u, hu, rfl⟩ := hVU i hv
      exact ⟨u, ⟨hu, hv⟩, rfl⟩

end

end ReciprocityTheory.AnForm.M
