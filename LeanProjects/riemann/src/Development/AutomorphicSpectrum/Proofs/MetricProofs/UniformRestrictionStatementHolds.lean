import Mathlib
import ReciprocityTheory.AnalyticForms.LeviForms.UnifInt
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PHyperplaneDivisible

open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Ar.Giv.Restrict

noncomputable section

open ReciprocityTheory.AnForm.M.SimpleNormalCrossingSliceCharts Set

variable {X : Type} [TopologicalSpace X]

theorem holoOn_continuousOn {e : ℕ} (A : FinHolAtlas e X) {U : Set X} {g : X → ℂ}
    (hg : A.HoloOn U g) (hU : IsOpen U) : ContinuousOn g U := by
  intro x hx
  obtain ⟨j, hj⟩ := A.cover x
  have hy : A.chart j x ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' U :=
    ⟨(A.chart j).map_source hj, by simpa [(A.chart j).left_inv hj] using hx⟩
  have h1 : ContinuousAt (g ∘ (A.chart j).symm) (A.chart j x) := (hg j _ hy).continuousAt
  have h2 : ContinuousAt ((g ∘ (A.chart j).symm) ∘ (A.chart j)) x :=
    ContinuousAt.comp h1 ((A.chart j).continuousAt hj)
  refine (h2.congr ?_).continuousWithinAt
  filter_upwards [(A.chart j).open_source.mem_nhds hj] with y hy
  simp [(A.chart j).left_inv hy]

theorem holoOn_comp {e e' : ℕ} {Y : Type} [TopologicalSpace Y] (B : FinHolAtlas e' Y)
    (A : FinHolAtlas e X) {h : Y → X} (hh : HoloMap B A h) {U : Set X} {g : X → ℂ}
    (hg : A.HoloOn U g) : B.HoloOn (h ⁻¹' U) (g ∘ h) := by
  intro j z ⟨hz, hzU⟩
  obtain ⟨k, hk⟩ := A.cover (h ((B.chart j).symm z))
  have hτ : AnalyticAt ℂ (A.chart k ∘ h ∘ (B.chart j).symm) z := hh.2 j k z ⟨hz, hk⟩
  have hgk : AnalyticAt ℂ (g ∘ (A.chart k).symm) ((A.chart k ∘ h ∘ (B.chart j).symm) z) :=
    hg k _ ⟨(A.chart k).map_source hk, by
      show (A.chart k).symm (A.chart k (h ((B.chart j).symm z))) ∈ U
      rw [(A.chart k).left_inv hk]; exact hzU⟩
  refine (hgk.comp hτ).congr ?_
  have hc : ContinuousAt (h ∘ (B.chart j).symm) z :=
    hh.1.continuousAt.comp ((B.chart j).continuousAt_symm hz)
  filter_upwards [hc.preimage_mem_nhds ((A.chart k).open_source.mem_nhds hk)] with z' hz'
  simp only [Function.comp_apply]
  rw [(A.chart k).left_inv (show h ((B.chart j).symm z') ∈ _ from hz')]

theorem holoOn_of_chart {e : ℕ} (A : FinHolAtlas e X)
    {ψ : OpenPartialHomeomorph X (Fin e → ℂ)} (hc : IsCompatChart A ψ) {W : Set X}
    (hW : W ⊆ ψ.source) {G : (Fin e → ℂ) → ℂ} (hG : ∀ y ∈ W, AnalyticAt ℂ G (ψ y)) :
    A.HoloOn W (fun y => G (ψ y)) := by
  intro j z ⟨hz, hzW⟩
  have h1 : AnalyticAt ℂ (ψ ∘ (A.chart j).symm) z := (hc j).1 z ⟨hz, hW hzW⟩
  exact AnalyticAt.comp (g := G) (f := ψ ∘ (A.chart j).symm) (hG _ hzW) h1

theorem subset_closure_ne {e : ℕ} (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) (i : Fin e)
    {S : Set X} (hS : IsOpen S) (hSs : S ⊆ ψ.source) : S ⊆ closure {y ∈ S | ψ y i ≠ 0} := by
  intro y hy
  have hΩ : IsOpen (ψ.target ∩ ψ.symm ⁻¹' S) := ψ.isOpen_inter_preimage_symm hS
  have hD : Dense {z : Fin e → ℂ | z i ≠ 0} :=
    (dense_compl_singleton (0 : ℂ)).preimage (isOpenMap_eval i)
  have hmem : ψ y ∈ ψ.target ∩ ψ.symm ⁻¹' S :=
    ⟨ψ.map_source (hSs hy), by
      show ψ.symm (ψ y) ∈ S
      rw [ψ.left_inv (hSs hy)]; exact hy⟩
  have hz : ψ y ∈ closure ((ψ.target ∩ ψ.symm ⁻¹' S) ∩ {z : Fin e → ℂ | z i ≠ 0}) :=
    hD.open_subset_closure_inter hΩ hmem
  have h1 := (ψ.continuousAt_symm hmem.1).continuousWithinAt.mem_closure_image hz
  rw [ψ.left_inv (hSs hy)] at h1
  refine closure_mono ?_ h1
  rintro _ ⟨z, ⟨⟨hz1, hz2⟩, hz3⟩, rfl⟩
  refine ⟨hz2, ?_⟩
  rw [ψ.right_inv hz1]
  exact hz3

theorem exists_quot {e : ℕ} (A : FinHolAtlas e X) {ψ φ : OpenPartialHomeomorph X (Fin e → ℂ)}
    (hψ : IsCompatChart A ψ) (hφ : IsCompatChart A φ) {i j : Fin e}
    (h0 : ∀ y ∈ ψ.source ∩ φ.source, ψ y i = 0 → φ y j = 0) :
    ∃ G : (Fin e → ℂ) → ℂ, (∀ y ∈ ψ.source ∩ φ.source, AnalyticAt ℂ G (ψ y)) ∧
      ∀ y ∈ ψ.source ∩ φ.source, φ y j = ψ y i * G (ψ y) := by
  have hΩ : IsOpen (ψ.target ∩ ψ.symm ⁻¹' φ.source) := ψ.isOpen_inter_preimage_symm φ.open_source
  have hF : AnalyticOnNhd ℂ (fun z => φ (ψ.symm z) j) (ψ.target ∩ ψ.symm ⁻¹' φ.source) :=
    fun z hz => ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin e => ℂ) j).analyticAt _).comp
      (compat_trans A hψ hφ hz.1 hz.2)
  have hmem : ∀ y ∈ ψ.source ∩ φ.source, ψ y ∈ ψ.target ∩ ψ.symm ⁻¹' φ.source := fun y hy =>
    ⟨ψ.map_source hy.1, by
      show ψ.symm (ψ y) ∈ φ.source
      rw [ψ.left_inv hy.1]; exact hy.2⟩
  obtain ⟨G, hG, hGe⟩ := GroundTheory.Heights₂.Heights.AnalyticLimit.HyperplaneDivisible.proof e _ _ i hΩ hF
    (fun z hz hzi => h0 _ ⟨ψ.map_target hz.1, hz.2⟩ (by rw [ψ.right_inv hz.1]; exact hzi))
  refine ⟨G, fun y hy => hG _ (hmem y hy), fun y hy => ?_⟩
  have := hGe _ (hmem y hy)
  simpa [ψ.left_inv hy.1] using this

theorem exists_unit {e : ℕ} (A : FinHolAtlas e X) {ψ φ : OpenPartialHomeomorph X (Fin e → ℂ)}
    (hψ : IsCompatChart A ψ) (hφ : IsCompatChart A φ) {i j : Fin e}
    (h0 : ∀ y ∈ ψ.source ∩ φ.source, ψ y i = 0 ↔ φ y j = 0) :
    ∃ h : X → ℂ, A.HoloOn (ψ.source ∩ φ.source) h ∧ (∀ y ∈ ψ.source ∩ φ.source, h y ≠ 0) ∧
      ∀ y ∈ ψ.source ∩ φ.source, φ y j = h y * ψ y i := by
  obtain ⟨G₁, hG₁, e₁⟩ := exists_quot A hψ hφ (i := i) (j := j) (fun y hy => (h0 y hy).1)
  obtain ⟨G₂, hG₂, e₂⟩ := exists_quot A hφ hψ (i := j) (j := i)
    (fun y hy => (h0 y ⟨hy.2, hy.1⟩).2)
  have hSo : IsOpen (ψ.source ∩ φ.source) := ψ.open_source.inter φ.open_source
  have H₁ : A.HoloOn (ψ.source ∩ φ.source) (fun y => G₁ (ψ y)) :=
    holoOn_of_chart A hψ inter_subset_left hG₁
  have H₂ : A.HoloOn (ψ.source ∩ φ.source) (fun y => G₂ (φ y)) :=
    holoOn_of_chart A hφ inter_subset_right (fun y hy => hG₂ y ⟨hy.2, hy.1⟩)
  have key : EqOn (fun y => G₁ (ψ y) * G₂ (φ y)) (fun _ => (1 : ℂ)) (ψ.source ∩ φ.source) := by
    refine Set.EqOn.of_subset_closure (s := {y ∈ ψ.source ∩ φ.source | ψ y i ≠ 0}) ?_
      ((holoOn_continuousOn A H₁ hSo).mul (holoOn_continuousOn A H₂ hSo)) continuousOn_const
      (fun y hy => hy.1) (subset_closure_ne ψ i hSo inter_subset_left)
    rintro y ⟨hy, hne⟩
    have a₁ := e₁ y hy
    have a₂ := e₂ y ⟨hy.2, hy.1⟩
    rw [a₁] at a₂
    have : ψ y i * (G₁ (ψ y) * G₂ (φ y)) = ψ y i * 1 := by rw [mul_one, ← mul_assoc, ← a₂]
    exact mul_left_cancel₀ hne this
  refine ⟨fun y => G₁ (ψ y), H₁, fun y hy h => ?_, fun y hy => ?_⟩
  · have := key hy
    simp [h] at this
  · rw [e₁ y hy, mul_comm]

theorem exists_sliceAtlas {e : ℕ} (A : FinHolAtlas (e + 1) X) (S : Set X) [CompactSpace S]
    (key : ∀ p : S, ∃ (ψ : OpenPartialHomeomorph X (Fin (e + 1) → ℂ)) (i : Fin (e + 1)),
      IsCompatChart A ψ ∧ p.1 ∈ ψ.source ∧ ∀ y ∈ ψ.source, y ∈ S ↔ ψ y i = 0) :
    ∃ B : FinHolAtlas e S, HoloMap B A Subtype.val ∧
      ∀ j, ∃ (ψ : OpenPartialHomeomorph X (Fin (e + 1) → ℂ)) (i : Fin (e + 1))
        (hS : ∀ y ∈ ψ.source, y ∈ S ↔ ψ y i = 0) (w : S),
        IsCompatChart A ψ ∧ B.chart j = sliceChart ψ i S hS w := by
  choose ψ i hc hp hS using key
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun p : S => (sliceChart (ψ p) (i p) S (hS p) p).source)
    (fun p => (sliceChart (ψ p) (i p) S (hS p) p).open_source)
    (fun w _ => mem_iUnion.2 ⟨w, hp w⟩)
  let f : Fin t.card → S := fun j => (t.equivFin.symm j).1
  refine ⟨⟨t.card, fun j => sliceChart (ψ (f j)) (i (f j)) S (hS (f j)) (f j), ?_, ?_⟩,
    ⟨continuous_subtype_val, fun j k' => slice_holo A S (hS (f j)) (f j) (hc (f j)) k'⟩,
    fun j => ⟨ψ (f j), i (f j), hS (f j), f j, hc (f j), rfl⟩⟩
  · intro w
    obtain ⟨p, hpt, hw⟩ := mem_iUnion₂.1 (ht (mem_univ w))
    refine ⟨t.equivFin ⟨p, hpt⟩, ?_⟩
    simpa [f] using hw
  · intro j j'
    exact slice_trans A S (hS (f j)) (hS (f j')) (f j) (f j') (hc (f j)) (hc (f j'))

theorem compat_restrOpen {e : ℕ} {A : FinHolAtlas e X}
    {ψ : OpenPartialHomeomorph X (Fin e → ℂ)} (hc : IsCompatChart A ψ) {V : Set X}
    (hV : IsOpen V) : IsCompatChart A (ψ.restrOpen V hV) := by
  intro j
  refine ⟨(hc j).1.mono ?_, (hc j).2.mono ?_⟩
  · rintro z ⟨hz, hz2⟩
    exact ⟨hz, hz2.1⟩
  · rintro z ⟨hz, hz2⟩
    exact ⟨hz.1, hz2⟩

theorem slice_compat {e : ℕ} {A : FinHolAtlas (e + 1) X} {S : Set X} {B : FinHolAtlas e S}
    (hch : ∀ j, ∃ (ψ : OpenPartialHomeomorph X (Fin (e + 1) → ℂ)) (i : Fin (e + 1))
        (hS : ∀ y ∈ ψ.source, y ∈ S ↔ ψ y i = 0) (w : S),
        IsCompatChart A ψ ∧ B.chart j = sliceChart ψ i S hS w)
    {ψ : OpenPartialHomeomorph X (Fin (e + 1) → ℂ)} {i : Fin (e + 1)}
    (hS : ∀ y ∈ ψ.source, y ∈ S ↔ ψ y i = 0) (w : S) (hc : IsCompatChart A ψ) :
    IsCompatChart B (sliceChart ψ i S hS w) := by
  intro j
  obtain ⟨ψ', i', hS', w', hc', hj⟩ := hch j
  rw [hj]
  exact ⟨slice_trans A S hS' hS w' w hc' hc, slice_trans A S hS hS' w w' hc hc'⟩

theorem slice_posPot {e : ℕ} (A : FinHolAtlas (e + 1) X) (S : Set X) (B : FinHolAtlas e S)
    (hB : HoloMap B A Subtype.val)
    (hch : ∀ j, ∃ (ψ : OpenPartialHomeomorph X (Fin (e + 1) → ℂ)) (i : Fin (e + 1))
        (hS : ∀ y ∈ ψ.source, y ∈ S ↔ ψ y i = 0) (w : S),
        IsCompatChart A ψ ∧ B.chart j = sliceChart ψ i S hS w)
    (Θ : LocPot X) (hΘ : IsPotential A Θ) (hpos : IsPosPot A Θ) :
    IsPosPot B (Θ.pullback Subtype.val hB.1) := by
  intro x j y hy w hw
  obtain ⟨ψ, i, hS, w0, hc, hj⟩ := hch j
  obtain ⟨hyt, hyU⟩ := hy
  have hyU' : ((B.chart j).symm y).1 ∈ Θ.U x.1 := hyU
  obtain ⟨k, hk⟩ := A.cover ((B.chart j).symm y).1
  have hτ : AnalyticAt ℂ (A.chart k ∘ Subtype.val ∘ (B.chart j).symm) y := hB.2 j k y ⟨hyt, hk⟩
  have hcont : ContinuousAt (Subtype.val ∘ (B.chart j).symm) y :=
    continuous_subtype_val.continuousAt.comp ((B.chart j).continuousAt_symm hyt)
  have hnear : ∀ᶠ z in 𝓝 y, ((B.chart j).symm z).1 ∈ (A.chart k).source :=
    hcont.preimage_mem_nhds ((A.chart k).open_source.mem_nhds hk)
  have hτmem : (A.chart k ∘ Subtype.val ∘ (B.chart j).symm) y ∈
      (A.chart k).target ∩ (A.chart k).symm ⁻¹' Θ.U x.1 :=
    ⟨(A.chart k).map_source hk, by
      show (A.chart k).symm (A.chart k ((B.chart j).symm y).1) ∈ Θ.U x.1
      rw [(A.chart k).left_inv hk]; exact hyU'⟩
  have hF : ContDiffAt ℝ 2 (Θ.φ x.1 ∘ (A.chart k).symm)
      ((A.chart k ∘ Subtype.val ∘ (B.chart j).symm) y) :=
    ((hΘ.1 x.1 k).contDiffAt (((A.chart k).isOpen_inter_preimage_symm
      (Θ.isOpen_U x.1)).mem_nhds hτmem)).of_le (WithTop.coe_le_coe.mpr le_top)
  have hgerm : ((Θ.pullback Subtype.val hB.1).φ x) ∘ (B.chart j).symm =ᶠ[𝓝 y]
      (Θ.φ x.1 ∘ (A.chart k).symm) ∘ (A.chart k ∘ Subtype.val ∘ (B.chart j).symm) := by
    filter_upwards [hnear] with z hz
    show Θ.φ x.1 ((B.chart j).symm z).1 =
      Θ.φ x.1 ((A.chart k).symm (A.chart k ((B.chart j).symm z).1))
    rw [(A.chart k).left_inv hz]
  rw [levi_congr hgerm w, levi_comp w hτ hF]
  refine hpos x.1 k _ hτmem _ ?_

  have hchart : ∀ p : S, B.chart j p = i.removeNth (ψ p.1) := fun p => by rw [hj]; rfl
  have hsrc : ∀ p : S, p ∈ (B.chart j).source → p.1 ∈ ψ.source := fun p hp => by
    rw [hj] at hp; exact hp
  have hqψ : ((B.chart j).symm y).1 ∈ ψ.source := hsrc _ ((B.chart j).map_target hyt)
  have hR : AnalyticAt ℂ (fun v => i.removeNth ((ψ ∘ (A.chart k).symm) v))
      ((A.chart k ∘ Subtype.val ∘ (B.chart j).symm) y) :=
    analyticAt_removeNth_comp i ((hc k).1 _ ⟨hτmem.1, by
      show (A.chart k).symm (A.chart k ((B.chart j).symm y).1) ∈ ψ.source
      rw [(A.chart k).left_inv hk]; exact hqψ⟩)
  have hev : (fun v => i.removeNth ((ψ ∘ (A.chart k).symm) v)) ∘
      (A.chart k ∘ Subtype.val ∘ (B.chart j).symm) =ᶠ[𝓝 y] id := by
    filter_upwards [hnear, (B.chart j).open_target.mem_nhds hyt] with z hz hzt
    show i.removeNth (ψ ((A.chart k).symm (A.chart k ((B.chart j).symm z).1))) = z
    rw [(A.chart k).left_inv hz, ← hchart, (B.chart j).right_inv hzt]
  have hcomp := fderiv_comp y hR.differentiableAt hτ.differentiableAt
  rw [hev.fderiv_eq, fderiv_id] at hcomp
  intro h0
  apply hw
  have := congrArg (fun T => T w) hcomp
  simpa [h0] using this

theorem coord_of_mem {e r : ℕ} {ψ : OpenPartialHomeomorph X (Fin e → ℂ)}
    {σ : Fin r → Option (Fin e)} {W : Fin r → Set X}
    (hW : ∀ k, W k ∩ ψ.source = {y ∈ ψ.source | ∃ i, σ k = some i ∧ ψ y i = 0}) (k : Fin r)
    {x : X} (hx : x ∈ W k) (hxs : x ∈ ψ.source) :
    ∃ i, σ k = some i ∧ ∀ y ∈ ψ.source, y ∈ W k ↔ ψ y i = 0 := by
  have hp : x ∈ W k ∩ ψ.source := ⟨hx, hxs⟩
  rw [hW k] at hp
  obtain ⟨-, i, hi, -⟩ := hp
  refine ⟨i, hi, fun y hy => ⟨fun hyW => ?_, fun h0 => ?_⟩⟩
  · have : y ∈ W k ∩ ψ.source := ⟨hyW, hy⟩
    rw [hW k] at this
    obtain ⟨-, i', hi', h0⟩ := this
    obtain rfl : i = i' := Option.some_injective _ (hi.symm.trans hi')
    exact h0
  · have : y ∈ {y ∈ ψ.source | ∃ i, σ k = some i ∧ ψ y i = 0} := ⟨hy, i, hi, h0⟩
    rw [← hW k] at this
    exact this.1

theorem local_div {e : ℕ} (A : FinHolAtlas e X) {ψ φ : OpenPartialHomeomorph X (Fin e → ℂ)}
    {i : Fin e} {a u u₂ h P : X → ℂ}
    (ha : ContinuousOn a (ψ.source ∩ φ.source))
    (hu : A.HoloOn ψ.source u) (hu0 : ∀ y ∈ ψ.source, u y ≠ 0)
    (hu₂ : A.HoloOn φ.source u₂) (hu₂0 : ∀ y ∈ φ.source, u₂ y ≠ 0)
    (hh : A.HoloOn (ψ.source ∩ φ.source) h) (hh0 : ∀ y ∈ ψ.source ∩ φ.source, h y ≠ 0)
    (hP : ContinuousOn P ψ.source)
    (he : ∀ y ∈ ψ.source ∩ φ.source, a y * (u₂ y * (h y * ψ y i)) = u y * (P y * ψ y i)) :
    ∃ t : X → ℂ, A.HoloOn (ψ.source ∩ φ.source) t ∧ (∀ y ∈ ψ.source ∩ φ.source, t y ≠ 0) ∧
      ∀ y ∈ ψ.source ∩ φ.source, a y = t y * P y := by
  have hSo : IsOpen (ψ.source ∩ φ.source) := ψ.open_source.inter φ.open_source
  have hu' : A.HoloOn (ψ.source ∩ φ.source) u := fun j => (hu j).mono fun z hz => ⟨hz.1, hz.2.1⟩
  have hu₂' : A.HoloOn (ψ.source ∩ φ.source) u₂ :=
    fun j => (hu₂ j).mono fun z hz => ⟨hz.1, hz.2.2⟩
  have hc1 := holoOn_continuousOn A hu' hSo
  have hc2 := holoOn_continuousOn A hu₂' hSo
  have hc3 := holoOn_continuousOn A hh hSo
  have key : EqOn (fun y => a y * (u₂ y * h y)) (fun y => u y * P y) (ψ.source ∩ φ.source) := by
    refine Set.EqOn.of_subset_closure (s := {y ∈ ψ.source ∩ φ.source | ψ y i ≠ 0}) ?_
      (ha.mul (hc2.mul hc3)) (hc1.mul (hP.mono inter_subset_left))
      (fun y hy => hy.1) (subset_closure_ne ψ i hSo inter_subset_left)
    rintro y ⟨hy, hne⟩
    have := he y hy
    refine mul_right_cancel₀ hne ?_
    calc a y * (u₂ y * h y) * ψ y i = a y * (u₂ y * (h y * ψ y i)) := by ring
      _ = u y * (P y * ψ y i) := this
      _ = u y * P y * ψ y i := by ring
  refine ⟨fun y => u y / (u₂ y * h y), fun j z hz => ?_, fun y hy => ?_, fun y hy => ?_⟩
  · have hy : (A.chart j).symm z ∈ ψ.source ∩ φ.source := hz.2
    exact (hu' j z hz).div ((hu₂' j z hz).mul (hh j z hz))
      (mul_ne_zero (hu₂0 _ hy.2) (hh0 _ hy))
  · exact div_ne_zero (hu0 _ hy.1) (mul_ne_zero (hu₂0 _ hy.2) (hh0 _ hy))
  · have h1 : u₂ y * h y ≠ 0 := mul_ne_zero (hu₂0 _ hy.2) (hh0 _ hy)
    have h2 := key hy
    show a y = u y / (u₂ y * h y) * P y
    rw [div_mul_eq_mul_div, eq_div_iff h1]
    exact h2

theorem slice_snc {e : ℕ} (A : FinHolAtlas (e + 1) X) (L L' : LocPot X) (s v : X → X → ℂ)
    {n : ℕ} (m : Fin n → ℕ) (W : Fin n → Set X) (Dg : Set X) (B : FinHolAtlas e Dg)
    (hB : HoloMap B A Subtype.val)
    (hch : ∀ j, ∃ (ψ : OpenPartialHomeomorph X (Fin (e + 1) → ℂ)) (i : Fin (e + 1))
        (hS : ∀ y ∈ ψ.source, y ∈ Dg ↔ ψ y i = 0) (w : Dg),
        IsCompatChart A ψ ∧ B.chart j = sliceChart ψ i Dg hS w)
    (hs : IsSection A L s) (hsv : IsSNC A L' v ![1] ![Dg])
    (hsnc : IsSNC A (L + L') (fun x y => s x y * v x y) (Fin.snoc m 1) (Fin.snoc W Dg)) :
    IsSNC B (L.pullback Subtype.val hB.1) (fun x y => s x.1 y.1) m
      (fun k => Subtype.val ⁻¹' W k) := by
  intro x
  obtain ⟨ψ, hψ, hxψ, hsub, σ, hinj, hW, u, hu, hu0, he⟩ := hsnc x.1
  obtain ⟨φ, hφ, hxφ, -, σ', -, hW', u₂, hu₂, hu₂0, he₂⟩ := hsv x.1
  have hsub' : ψ.source ⊆ L.U x.1 ∩ L'.U x.1 := hsub
  obtain ⟨i, hi, hiS⟩ := coord_of_mem hW (Fin.last n) (x := x.1) (by simpa using x.2) hxψ
  obtain ⟨j, hj, hjS⟩ := coord_of_mem hW' 0 (x := x.1) x.2 hxφ
  have hiS' : ∀ y ∈ ψ.source, y ∈ Dg ↔ ψ y i = 0 := by simpa using hiS
  have hjS' : ∀ y ∈ φ.source, y ∈ Dg ↔ φ y j = 0 := hjS
  obtain ⟨h, hh, hh0, hhe⟩ := exists_unit A hψ hφ (i := i) (j := j)
    (fun y hy => (hiS' y hy.1).symm.trans (hjS' y hy.2))
  let P : X → ℂ := fun y => ∏ k : Fin n, (match σ k.castSucc with
    | some a => ψ y a ^ m k
    | none => 1)
  have hP : ContinuousOn P ψ.source := continuousOn_finset_prod _ fun k _ => by
    cases σ k.castSucc with
    | none => exact continuousOn_const
    | some a => exact ((continuous_apply a).comp_continuousOn ψ.continuousOn).pow _
  have he' : ∀ y ∈ ψ.source, s x.1 y * v x.1 y = u y * (P y * ψ y i) := by
    intro y hy
    have := he y hy
    rw [Fin.prod_univ_castSucc] at this
    simp [hi] at this
    rw [this]
    refine congrArg (fun w => u y * (w * ψ y i)) (Finset.prod_congr rfl fun k _ => ?_)
    generalize σ k.castSucc = o
    cases o <;> rfl
  have he₂' : ∀ y ∈ φ.source, v x.1 y = u₂ y * φ y j := by
    intro y hy
    have := he₂ y hy
    simpa [hj] using this
  have hsc : ContinuousOn (s x.1) (ψ.source ∩ φ.source) :=
    (holoOn_continuousOn A (hs.1 x.1) (L.isOpen_U x.1)).mono fun y hy => (hsub' hy.1).1
  obtain ⟨t, ht, ht0, hte⟩ := local_div A hsc hu hu0 hu₂ hu₂0 hh hh0 hP (fun y hy => by
    rw [← hhe y hy, ← he₂' y hy.2]; exact he' y hy.1)
  have hne : ∀ k : Fin n, ∃ o : Option (Fin e), σ k.castSucc = o.map i.succAbove := by
    intro k
    rcases hk : σ k.castSucc with _ | a
    · exact ⟨none, rfl⟩
    · have hai : a ≠ i := by
        rintro rfl
        exact (Fin.castSucc_lt_last k).ne (hinj _ _ _ hk hi)
      obtain ⟨l, rfl⟩ := Fin.exists_succAbove_eq hai
      exact ⟨some l, rfl⟩
  choose σ₂ hσ₂ using hne
  have hWc : ∀ (k : Fin n), ∀ y ∈ ψ.source,
      (y ∈ W k ↔ ∃ a, σ k.castSucc = some a ∧ ψ y a = 0) := by
    intro k y hy
    have hk := hW k.castSucc
    constructor
    · intro hyW
      have hm : y ∈ (Fin.snoc W Dg : Fin (n + 1) → Set X) k.castSucc ∩ ψ.source :=
        ⟨by simpa using hyW, hy⟩
      rw [hk] at hm
      exact hm.2
    · intro hh'
      have hm : y ∈ {y ∈ ψ.source | ∃ i, σ k.castSucc = some i ∧ ψ y i = 0} := ⟨hy, hh'⟩
      rw [← hk] at hm
      simpa using hm.1
  have hc₀ := compat_restrOpen hψ φ.open_source
  have hsrc₀ : (ψ.restrOpen φ.source φ.open_source).source = ψ.source ∩ φ.source :=
    ψ.restrOpen_source _ _
  have hS₀ : ∀ y ∈ (ψ.restrOpen φ.source φ.open_source).source,
      y ∈ Dg ↔ (ψ.restrOpen φ.source φ.open_source) y i = 0 :=
    fun y hy => hiS' y (hsrc₀ ▸ hy).1
  have hmemS : ∀ y : Dg, y ∈ (sliceChart (ψ.restrOpen φ.source φ.open_source) i Dg hS₀ x).source ↔
      y.1 ∈ ψ.source ∩ φ.source := fun y => by
    rw [← hsrc₀]; rfl
  refine ⟨sliceChart (ψ.restrOpen φ.source φ.open_source) i Dg hS₀ x,
    slice_compat hch hS₀ x hc₀, (hmemS x).2 ⟨hxψ, hxφ⟩,
    fun y hy => (hsub' ((hmemS y).1 hy).1).1, σ₂, ?_, ?_, t ∘ Subtype.val, ?_, ?_, ?_⟩
  · intro k k' l h1 h2
    have h1' : σ k.castSucc = some (i.succAbove l) := by rw [hσ₂, h1]; rfl
    have h2' : σ k'.castSucc = some (i.succAbove l) := by rw [hσ₂, h2]; rfl
    exact Fin.castSucc_injective _ (hinj _ _ _ h1' h2')
  · intro k
    ext y
    constructor
    · rintro ⟨hyW, hys⟩
      have hy1 := (hmemS y).1 hys
      obtain ⟨a, ha, h0⟩ := (hWc k y.1 hy1.1).1 hyW
      rw [hσ₂ k] at ha
      cases hk : σ₂ k with
      | none => rw [hk] at ha; simp at ha
      | some l =>
        rw [hk] at ha
        simp only [Option.map_some, Option.some.injEq] at ha
        subst ha
        exact ⟨hys, l, rfl, h0⟩
    · rintro ⟨hys, l, hl, h0⟩
      have hy1 := (hmemS y).1 hys
      exact ⟨(hWc k y.1 hy1.1).2 ⟨i.succAbove l, by rw [hσ₂, hl]; rfl, h0⟩, hys⟩
  · have hse : (sliceChart (ψ.restrOpen φ.source φ.open_source) i Dg hS₀ x).source =
        Subtype.val ⁻¹' (ψ.source ∩ φ.source) := by
      ext y; exact hmemS y
    rw [hse]
    exact holoOn_comp B A hB ht
  · exact fun y hy => ht0 _ ((hmemS y).1 hy)
  · intro y hy
    show s x.1 y.1 = t y.1 * _
    rw [hte _ ((hmemS y).1 hy)]
    refine congrArg (t y.1 * ·) (Finset.prod_congr rfl fun k _ => ?_)
    have h := hσ₂ k
    revert h
    generalize σ k.castSucc = o1
    generalize σ₂ k = o2
    intro h
    subst h
    cases o2 <;> rfl

end

end GlobalTheory.CompanionTheory.Ar.Giv.Restrict

namespace GlobalTheory.CompanionTheory.Ar.Giv

open GlobalTheory.CompanionTheory.Ar.Giv.Restrict ReciprocityTheory.AnForm.M.SimpleNormalCrossingSliceCharts

theorem unifRestrict : UnifRestrictStatement := by
  intro e X _ _ _ A Θ L s n m W hΘ hpos hL hs L' v Dg hL' hv hsv hsnc
  have hcl : IsClosed Dg := isClosed_divisorComponent A L' v ![1] ![Dg] hsv 0
  haveI : CompactSpace Dg := isCompact_iff_compactSpace.mp hcl.isCompact
  obtain ⟨B, hB, hch⟩ := exists_sliceAtlas A Dg (fun p => by
    obtain ⟨ψ, hc, hp, -, σ, -, hW, -⟩ := hsv p.1
    obtain ⟨i, -, hi⟩ := coord_of_mem hW 0 (x := p.1) p.2 hp
    exact ⟨ψ, i, hc, hp, hi⟩)
  exact ⟨B, hB, n, m, fun k => Subtype.val ⁻¹' W k, isPotentialPullback A B _ hB Θ hΘ,
    slice_posPot A Dg B hB hch Θ hΘ hpos, slice_snc A L L' s v m W Dg B hB hch hs hsv hsnc⟩

end GlobalTheory.CompanionTheory.Ar.Giv
