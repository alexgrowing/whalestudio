import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.MeasurableSetImageOfIsLocalHomeomorph
import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.TsupportDbSubset

namespace ReciprocityTheory.L2DbarEstimates

open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal

noncomputable section

def chartSlice {M : Type*} [TopologicalSpace M] {n : ℕ} (e : OpenPartialHomeomorph M (V n))
    {p : ℕ} (i : Fin p) : OpenPartialHomeomorph (M × Fin p) (V n) where
  toFun q := e q.1
  invFun y := (e.symm y, i)
  source := e.source ×ˢ {i}
  target := e.target
  map_source' _q hq := e.map_source hq.1
  map_target' _y hy := ⟨e.map_target hy, rfl⟩
  left_inv' _q hq := Prod.ext (e.left_inv hq.1) (Set.mem_singleton_iff.1 hq.2).symm
  right_inv' _y hy := e.right_inv hy
  open_source := e.open_source.prod (isOpen_discrete _)
  open_target := e.open_target
  continuousOn_toFun := e.continuousOn.comp continuousOn_fst (fun _q hq => hq.1)
  continuousOn_invFun := e.continuousOn_symm.prodMk continuousOn_const

theorem chartSlice_symm_apply {M : Type*} [TopologicalSpace M] {n : ℕ}
    (e : OpenPartialHomeomorph M (V n)) {p : ℕ} (i : Fin p) (y : V n) :
    (chartSlice e i).symm y = (e.symm y, i) := rfl

theorem isChart_chartSlice {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (e : OpenPartialHomeomorph M (V n)) (he : IsChart n z e) (p : ℕ) (i : Fin p) :
    IsChart n (fun q : M × Fin p => z q.1) (chartSlice e i) := by
  intro q hq
  exact he hq.1

theorem isLocalHomeomorph_comp_fst {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (hz : IsLocalHomeomorph z) (p : ℕ) :
    IsLocalHomeomorph (fun q : M × Fin p => z q.1) := by
  intro q
  obtain ⟨e, hx, he⟩ := hz q.1
  refine ⟨chartSlice e q.2, ⟨hx, rfl⟩, ?_⟩
  funext r
  rw [he]
  rfl

theorem chart_prodFin_local {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (hz : IsLocalHomeomorph z) (p : ℕ)
    (E : OpenPartialHomeomorph (M × Fin p) (V n)) (hE : IsChart n (fun q : M × Fin p => z q.1) E)
    (y : V n) (hy : y ∈ E.target) :
    ∃ (e : OpenPartialHomeomorph M (V n)) (i : Fin p), IsChart n z e ∧ y ∈ e.target ∧
      (E.symm : V n → M × Fin p) =ᶠ[𝓝 y] fun w => (e.symm w, i) := by
  set q := E.symm y with hq
  have hqs : q ∈ E.source := E.map_target hy
  obtain ⟨e, he, hxe⟩ := exists_chart n z hz q.1
  have hcont : ContinuousAt E.symm y := E.continuousAt_symm hy
  have hzq : z q.1 = y := by
    have h1 : z q.1 = E q := hE hqs
    rw [h1]; exact E.right_inv hy
  refine ⟨e, q.2, he, ?_, ?_⟩
  · rw [← hzq, he hxe]; exact e.map_source hxe
  · have t1 : ∀ᶠ w in 𝓝 y, (E.symm w).1 ∈ e.source :=
      (continuous_fst.continuousAt.comp hcont).preimage_mem_nhds (e.open_source.mem_nhds hxe)
    have t2 : ∀ᶠ w in 𝓝 y, (E.symm w).2 = q.2 :=
      (continuous_snd.continuousAt.comp hcont).preimage_mem_nhds ((isOpen_discrete {q.2}).mem_nhds rfl)
    have t3 : ∀ᶠ w in 𝓝 y, w ∈ E.target := E.open_target.mem_nhds hy
    filter_upwards [t1, t2, t3] with w h1 h2 h3
    have hz1 : z (E.symm w).1 = w := by
      have h4 : z (E.symm w).1 = E (E.symm w) := hE (E.map_target h3)
      rw [h4, E.right_inv h3]
    refine Prod.ext ?_ h2
    calc (E.symm w).1 = e.symm (e (E.symm w).1) := (e.left_inv h1).symm
      _ = e.symm w := by rw [← he h1, hz1]

theorem smooth_prodFin_iff {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (hz : IsLocalHomeomorph z) (p : ℕ) (F : M × Fin p → ℂ) :
    Smooth n (fun q : M × Fin p => z q.1) F ↔ ∀ i, Smooth n z (fun x => F (x, i)) := by
  constructor
  · intro h i e he
    exact h (chartSlice e i) (isChart_chartSlice n z e he p i)
  · intro h E hE y hy
    obtain ⟨e, i, he, hye, hev⟩ := chart_prodFin_local n z hz p E hE y hy
    have h1 : ContDiffAt ℝ ∞ ((fun x => F (x, i)) ∘ e.symm) y :=
      (h i e he).contDiffAt (e.open_target.mem_nhds hye)
    exact (h1.congr_of_eventuallyEq (hev.fun_comp F)).contDiffWithinAt

theorem ck_prodFin_iff {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (hz : IsLocalHomeomorph z) (p k : ℕ) (F : M × Fin p → ℂ) :
    Ck n (fun q : M × Fin p => z q.1) k F ↔ ∀ i, Ck n z k (fun x => F (x, i)) := by
  constructor
  · intro h i e he
    exact h (chartSlice e i) (isChart_chartSlice n z e he p i)
  · intro h E hE y hy
    obtain ⟨e, i, he, hye, hev⟩ := chart_prodFin_local n z hz p E hE y hy
    have h1 : ContDiffAt ℝ k ((fun x => F (x, i)) ∘ e.symm) y :=
      (h i e he).contDiffAt (e.open_target.mem_nhds hye)
    exact (h1.congr_of_eventuallyEq (hev.fun_comp F)).contDiffWithinAt

theorem holo_prodFin_iff {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (hz : IsLocalHomeomorph z) (p : ℕ) (F : M × Fin p → ℂ) :
    Holo n (fun q : M × Fin p => z q.1) F ↔ ∀ i, Holo n z (fun x => F (x, i)) := by
  constructor
  · intro h i e he
    exact h (chartSlice e i) (isChart_chartSlice n z e he p i)
  · intro h E hE y hy
    obtain ⟨e, i, he, hye, hev⟩ := chart_prodFin_local n z hz p E hE y hy
    have h1 : DifferentiableAt ℂ ((fun x => F (x, i)) ∘ e.symm) y :=
      (h i e he).differentiableAt (e.open_target.mem_nhds hye)
    exact (h1.congr_of_eventuallyEq (hev.fun_comp F)).differentiableWithinAt

theorem d_prodFin {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (hz : IsLocalHomeomorph z) (p : ℕ) (j : Fin n) (F : M × Fin p → ℂ) (x : M) (i : Fin p) :
    d n (fun q : M × Fin p => z q.1) j F (x, i) = d n z j (fun y => F (y, i)) x := by
  obtain ⟨e, he, hx⟩ := exists_chart n z hz x
  rw [d_eq_wd n _ (chartSlice e i) (isChart_chartSlice n z e he p i) j F (x, i) ⟨hx, rfl⟩,
    d_eq_wd n z e he j _ x hx]
  rfl

theorem db_prodFin {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (hz : IsLocalHomeomorph z) (p : ℕ) (j : Fin n) (F : M × Fin p → ℂ) (x : M) (i : Fin p) :
    db n (fun q : M × Fin p => z q.1) j F (x, i) = db n z j (fun y => F (y, i)) x := by
  obtain ⟨e, he, hx⟩ := exists_chart n z hz x
  rw [db_eq_wdb n _ (chartSlice e i) (isChart_chartSlice n z e he p i) j F (x, i) ⟨hx, rfl⟩,
    db_eq_wdb n z e he j _ x hx]
  rfl

theorem levi_prodFin {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (hz : IsLocalHomeomorph z) (p : ℕ) (ph : M × Fin p → ℝ) (x : M) (i : Fin p) (ξ : Fin n → ℂ) :
    Levi n (fun q : M × Fin p => z q.1) ph (x, i) ξ = Levi n z (fun y => ph (y, i)) x ξ := by
  obtain ⟨e, he, hx⟩ := exists_chart n z hz x
  rw [levi_eq_leviV n _ (chartSlice e i) (isChart_chartSlice n z e he p i) ph (x, i) ⟨hx, rfl⟩ ξ,
    levi_eq_leviV n z e he _ x hx ξ]
  rfl

theorem volFun_prod_singleton {M : Type*} (n : ℕ) (z : M → V n) (p : ℕ) (B : Set M) (i : Fin p) :
    volFun n (fun q : M × Fin p => z q.1) (B ×ˢ {i}) = volFun n z B := by
  unfold volFun
  refine lintegral_congr fun y => ?_
  have h : (B ×ˢ {i}) ∩ (fun q : M × Fin p => z q.1) ⁻¹' {y} = (fun x => (x, i)) '' (B ∩ z ⁻¹' {y}) := by
    ext ⟨x, j⟩
    simp only [Set.mem_inter_iff, Set.mem_prod, Set.mem_singleton_iff, Set.mem_preimage,
      Set.mem_image, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨hx, rfl⟩, hy⟩
      exact ⟨x, ⟨hx, hy⟩, rfl, rfl⟩
    · rintro ⟨x', ⟨hx, hy⟩, rfl, rfl⟩
      exact ⟨⟨hx, rfl⟩, hy⟩
  rw [h, (Prod.mk_left_injective i).encard_image]

theorem vol_prodFin_eq {M : Type*} [TopologicalSpace M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] (n : ℕ) (z : M → V n) (hz : IsLocalHomeomorph z) (p : ℕ) :
    vol n (fun q : M × Fin p => z q.1) = ∑ i, (vol n z).map (fun x => (x, i)) := by
  ext A hA
  have hz' := isLocalHomeomorph_comp_fst n z hz p
  have hS : ∀ i : Fin p, MeasurableSet ((fun x => (x, i)) ⁻¹' A) := fun i =>
    (measurable_id.prodMk measurable_const) hA
  have hA' : A = ⋃ i : Fin p, ((fun x => (x, i)) ⁻¹' A) ×ˢ {i} := by
    ext ⟨x, j⟩
    simp
  rw [Measure.coe_finset_sum, Finset.sum_apply]
  conv_lhs => rw [hA']
  rw [measure_iUnion (fun i j hij => Set.disjoint_left.2 fun q hq1 hq2 => hij (hq1.2.symm.trans hq2.2))
    (fun i => (hS i).prod (measurableSet_singleton i)), tsum_fintype]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Measure.map_apply (f := fun x => (x, i)) (measurable_id.prodMk measurable_const) hA,
    vol_apply n _ hz' _ ((hS i).prod (measurableSet_singleton i)), volFun_prod_singleton,
    vol_apply n z hz _ (hS i)]

theorem lintegral_vol_prodFin {M : Type*} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] (n : ℕ) (z : M → V n) (hz : IsLocalHomeomorph z) (p : ℕ) (f : M × Fin p → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ q, f q ∂vol n (fun q : M × Fin p => z q.1) = ∑ i, ∫⁻ x, f (x, i) ∂vol n z := by
  rw [vol_prodFin_eq n z hz p, lintegral_finset_sum_measure]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact lintegral_map hf (measurable_id.prodMk measurable_const)

theorem integral_vol_prodFin {M : Type*} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] (n : ℕ) (z : M → V n) (hz : IsLocalHomeomorph z) (p : ℕ) (f : M × Fin p → ℂ) (hf : Integrable f (vol n (fun q : M × Fin p => z q.1))) :
    ∫ q, f q ∂vol n (fun q : M × Fin p => z q.1) = ∑ i, ∫ x, f (x, i) ∂vol n z := by
  rw [vol_prodFin_eq n z hz p] at hf ⊢
  rw [integral_finset_sum_measure (integrable_finset_sum_measure.1 hf)]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact integral_map (measurable_id.prodMk measurable_const).aemeasurable
    (integrable_finset_sum_measure.1 hf i (Finset.mem_univ _)).aestronglyMeasurable

def EtaleStein.prodFin {M : Type*} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [MeasurableSpace M] [BorelSpace M] (n : ℕ) (X : EtaleStein n M) (p : ℕ) :
    EtaleStein n (M × Fin p) where
  z q := X.z q.1
  isLocalHomeomorph := isLocalHomeomorph_comp_fst n X.z X.isLocalHomeomorph p
  e q := X.e q.1
  smooth_e := (smooth_prodFin_iff n X.z X.isLocalHomeomorph p _).2 fun _ => X.smooth_e
  levi_e := by
    rintro ⟨x, i⟩ ξ
    rw [levi_prodFin n X.z X.isLocalHomeomorph p]
    exact X.levi_e x ξ
  isCompact_le a := by
    have h : {q : M × Fin p | X.e q.1 ≤ a} = {x | X.e x ≤ a} ×ˢ (Set.univ : Set (Fin p)) := by
      ext q; simp
    rw [h]
    exact (X.isCompact_le a).prod isCompact_univ

theorem EtaleStein.prodFin_proj {M : Type*} [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] (n : ℕ) (X : EtaleStein n M)
    (p : ℕ) : (EtaleStein.prodFin n X p).z = fun q => X.z q.1 := rfl

end

end ReciprocityTheory.L2DbarEstimates
