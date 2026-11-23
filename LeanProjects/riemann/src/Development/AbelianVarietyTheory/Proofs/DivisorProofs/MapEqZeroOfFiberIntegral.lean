import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TranslationInvariantSchwartzBruhatMapFactorsInte

open MeasureTheory ValuativeRel GlobalTheory.SplitWeil GlobalTheory.SplitWeil.HaarFactor
open scoped Topology

noncomputable section
namespace GlobalTheory.DetEqv.Transl

theorem mem_SB_of_compact {X : Type*} [TopologicalSpace X] {f : X → ℂ} (hf : IsLocallyConstant f) {K : Set X}
    (hK : IsCompact K) (h : ∀ x ∉ K, f x = 0) : f ∈ SB X := by
  refine ⟨hf, ?_⟩
  have hcl : IsClosed (Function.support f) := by
    have : Function.support f = (f ⁻¹' {0})ᶜ := by ext x; simp
    rw [this]
    exact (hf _).isClosed_compl
  refine hK.of_isClosed_subset (isClosed_tsupport f) ?_
  rw [tsupport, hcl.closure_eq]
  intro x hx
  by_contra hx'
  exact hx (h x hx')

section General
variable {A Z : Type*} [TopologicalSpace Z] [AddCommGroup A] [TopologicalSpace A]

omit [AddCommGroup A] in
theorem slice_mem' {G : A × Z → ℂ} (hG : G ∈ SB (A × Z)) (c : A) : (fun z => G (c, z)) ∈ SB Z :=
  mem_SB_of_compact (hG.1.comp_continuous (by fun_prop)) (hG.2.image continuous_snd) fun z hz =>
    image_eq_zero_of_notMem_tsupport fun h => hz ⟨(c, z), h, rfl⟩

omit [AddCommGroup A] in
theorem tens_mem' {φ : A → ℂ} (hφ : φ ∈ SB A) {f : Z → ℂ} (hf : f ∈ SB Z) :
    (fun y : A × Z => f y.2 * φ y.1) ∈ SB (A × Z) := by
  refine mem_SB_of_compact ((hf.1.comp_continuous continuous_snd).mul (hφ.1.comp_continuous continuous_fst))
    (hφ.2.prod hf.2) fun z hz => ?_
  rcases not_and_or.mp (Set.mem_prod.not.mp hz) with h | h
  · rw [image_eq_zero_of_notMem_tsupport h, mul_zero]
  · rw [image_eq_zero_of_notMem_tsupport h, zero_mul]

variable [IsTopologicalAddGroup A]

theorem transl_mem' {G : A × Z → ℂ} (hG : G ∈ SB (A × Z)) (c : A) :
    (fun y : A × Z => G (y.1 - c, y.2)) ∈ SB (A × Z) := by
  refine ⟨hG.1.comp_continuous (by fun_prop), ?_⟩
  exact hG.2.comp_homeomorph ((Homeomorph.subRight c).prodCongr (Homeomorph.refl Z))

theorem exists_subgroup_invariant'
    (hbasis : ∀ V ∈ 𝓝 (0 : A), ∃ U : AddSubgroup A, IsOpen (U : Set A) ∧ IsCompact (U : Set A) ∧ (U : Set A) ⊆ V)
    {G : A × Z → ℂ} (hG : G ∈ SB (A × Z)) :
    ∃ U : AddSubgroup A, IsOpen (U : Set A) ∧ IsCompact (U : Set A) ∧
      ∀ u ∈ U, ∀ y : A × Z, G (y.1 + u, y.2) = G y := by
  have h1 : ∀ᶠ t in 𝓝 (0 : A), ∀ y ∈ tsupport G, G (y.1 + t, y.2) = G y := by
    refine IsCompact.eventually_forall_of_forall_eventually hG.2 fun z _ => ?_
    have h2 : IsLocallyConstant fun q : A × (A × Z) => (G (q.2.1 + q.1, q.2.2), G q.2) :=
      (hG.1.comp_continuous (by fun_prop)).prodMk (hG.1.comp_continuous continuous_snd)
    filter_upwards [h2.eventually_eq (0, z)] with q hq
    simp only [Prod.mk.injEq, add_zero, Prod.mk.eta] at hq
    rw [hq.1, hq.2]
  obtain ⟨U, hUo, hUc, hUs⟩ := hbasis _ h1
  refine ⟨U, hUo, hUc, fun u hu z => ?_⟩
  by_cases hz : z ∈ tsupport G
  · exact hUs hu z hz
  by_cases hz' : (z.1 + u, z.2) ∈ tsupport G
  · have := hUs (U.neg_mem hu) _ hz'
    simp only [add_neg_cancel_right, Prod.mk.eta] at this
    exact this.symm
  · rw [image_eq_zero_of_notMem_tsupport hz, image_eq_zero_of_notMem_tsupport hz']

theorem exists_decomp' {U : AddSubgroup A} (hU : IsOpen (U : Set A)) {G : A × Z → ℂ} (hG : G ∈ SB (A × Z))
    (hinv : ∀ u ∈ U, ∀ y : A × Z, G (y.1 + u, y.2) = G y) :
    ∃ T : Finset (A ⧸ U), ∀ y : A × Z,
      G y = ∑ q ∈ T, G (q.out, y.2) * (U : Set A).indicator (fun _ => (1 : ℂ)) (y.1 - q.out) := by
  classical
  have hK : IsCompact (Prod.fst '' tsupport G) := hG.2.image continuous_fst
  obtain ⟨t, -, ht⟩ := hK.elim_nhds_subcover (fun a => (fun b => b - a) ⁻¹' (U : Set A))
    (fun a _ => (hU.preimage (by fun_prop)).mem_nhds (by simp))
  refine ⟨t.image (QuotientAddGroup.mk : A → A ⧸ U), fun z => ?_⟩
  have hind : ∀ q : A ⧸ U, (U : Set A).indicator (fun _ => (1 : ℂ)) (z.1 - q.out) =
      if (z.1 : A ⧸ U) = q then 1 else 0 := by
    intro q
    have : (z.1 : A ⧸ U) = q ↔ z.1 - q.out ∈ U := by
      conv_lhs => rw [← QuotientAddGroup.out_eq' q]
      exact QuotientAddGroup.eq_iff_sub_mem
    by_cases h : z.1 - q.out ∈ U
    · rw [Set.indicator_of_mem (show z.1 - q.out ∈ (U : Set A) from h), if_pos (this.mpr h)]
    · rw [Set.indicator_of_notMem (show z.1 - q.out ∉ (U : Set A) from h), if_neg (fun h' => h (this.mp h'))]
  simp only [hind, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq]
  split_ifs with h
  · have h2 : -z.1 + (z.1 : A ⧸ U).out ∈ U := QuotientAddGroup.eq.mp (QuotientAddGroup.out_eq' _).symm
    have := hinv _ h2 z
    rw [add_neg_cancel_left] at this
    exact this.symm
  · refine image_eq_zero_of_notMem_tsupport fun hz => h ?_
    obtain ⟨a, ha, hza⟩ := Set.mem_iUnion₂.mp (ht ⟨z, hz, rfl⟩)
    exact Finset.mem_image.mpr ⟨a, ha, (QuotientAddGroup.eq_iff_sub_mem.mpr hza).symm⟩

variable [T2Space A] [MeasurableSpace A] [BorelSpace A] (μ : Measure A) [μ.IsAddHaarMeasure]

omit [TopologicalSpace Z] in

theorem fiber_integral' {U : AddSubgroup A} (hUo : IsOpen (U : Set A)) (hUc : IsCompact (U : Set A))
    {G : A × Z → ℂ} (T : Finset (A ⧸ U))
    (hT : ∀ y : A × Z, G y = ∑ q ∈ T, G (q.out, y.2) * (U : Set A).indicator (fun _ => (1 : ℂ)) (y.1 - q.out))
    (z : Z) : ∫ a, G (a, z) ∂μ = (∑ q ∈ T, G (q.out, z)) * (μ.real (U : Set A) : ℂ) := by
  have he := integrable_of_SB μ (ind_mem hUo hUc)
  have hshift : ∀ c : A, ∫ a, (U : Set A).indicator (fun _ => (1 : ℂ)) (a - c) ∂μ = (μ.real (U : Set A) : ℂ) := by
    intro c
    rw [integral_sub_right_eq_self (fun a => (U : Set A).indicator (fun _ => (1 : ℂ)) a) c,
      integral_indicator_const _ hUo.measurableSet]
    simp
  calc ∫ a, G (a, z) ∂μ
      = ∫ a, ∑ q ∈ T, G (q.out, z) * (U : Set A).indicator (fun _ => (1 : ℂ)) (a - q.out) ∂μ :=
        integral_congr_ae (Filter.Eventually.of_forall fun a => hT (a, z))
    _ = (∑ q ∈ T, G (q.out, z)) * (μ.real (U : Set A) : ℂ) := by
      rw [integral_finsetSum _ fun q _ => (he.comp_sub_right _).const_mul _]
      simp only [integral_const_mul, hshift, ← Finset.sum_mul]

theorem map_eq_zero_of_fiber'
    (hbasis : ∀ V ∈ 𝓝 (0 : A), ∃ U : AddSubgroup A, IsOpen (U : Set A) ∧ IsCompact (U : Set A) ∧ (U : Set A) ⊆ V)
    (L : SB (A × Z) →ₗ[ℂ] ℂ)
    (hL : ∀ (c : A) (G G' : SB (A × Z)), (∀ u z, G'.1 (u, z) = G.1 (u + c, z)) → L G' = L G)
    (G : SB (A × Z)) (hG : ∀ z, ∫ a, G.1 (a, z) ∂μ = 0) : L G = 0 := by
  obtain ⟨U, hUo, hUc, hinv⟩ := exists_subgroup_invariant' hbasis G.2
  obtain ⟨T, hT⟩ := exists_decomp' hUo G.2 hinv
  have hsum : ∀ z, ∑ q ∈ T, G.1 (q.out, z) = 0 := fun z => by
    have := (fiber_integral' μ hUo hUc T hT z).symm.trans (hG z)
    exact (mul_eq_zero.mp this).resolve_right (real_ne_zero μ hUo hUc)
  let H : A ⧸ U → SB (A × Z) := fun q =>
    ⟨fun y => G.1 (q.out, y.2) * (U : Set A).indicator (fun _ => (1 : ℂ)) y.1,
      tens_mem' (ind_mem hUo hUc) (slice_mem' G.2 q.out)⟩
  let Gq : A ⧸ U → SB (A × Z) := fun q =>
    ⟨fun y => (H q).1 (y.1 - q.out, y.2), transl_mem' (H q).2 q.out⟩
  have hdec : G = ∑ q ∈ T, Gq q := by
    apply Subtype.ext
    funext z
    rw [hT z, Submodule.coe_sum, Finset.sum_apply]
  have hq : ∀ q, L (Gq q) = L (H q) := fun q =>
    (hL q.out (Gq q) (H q) fun u z => by simp [Gq]).symm
  have hg : ∑ q ∈ T, H q = 0 := by
    apply Subtype.ext
    funext y
    rw [Submodule.coe_sum, Finset.sum_apply]
    show ∑ q ∈ T, G.1 (q.out, y.2) * (U : Set A).indicator (fun _ => (1 : ℂ)) y.1 = 0
    rw [← Finset.sum_mul, hsum, zero_mul]
  rw [hdec, map_sum, Finset.sum_congr rfl fun q _ => hq q, ← map_sum, hg, map_zero]

end General

theorem map_eq_zero_of_fiber_integral : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : MeasureTheory.Measure k) [ν.IsAddHaarMeasure]
    (Z : Type) [TopologicalSpace Z] (p : ℕ) (L : GlobalTheory.SplitWeil.SB ((Fin p → k) × Z) →ₗ[ℂ] ℂ),
      (∀ (c : Fin p → k) (Φ Φ' : GlobalTheory.SplitWeil.SB ((Fin p → k) × Z)),
        (∀ (u : Fin p → k) (z : Z), (Φ' : (Fin p → k) × Z → ℂ) (u, z) = (Φ : (Fin p → k) × Z → ℂ) (u + c, z)) → L Φ' = L Φ) →
      ∀ Φ : GlobalTheory.SplitWeil.SB ((Fin p → k) × Z),
        (∀ z : Z, ∫ u, (Φ : (Fin p → k) × Z → ℂ) (u, z) ∂(MeasureTheory.Measure.pi fun _ : Fin p => ν) = 0) → L Φ = 0 := by
  intro k _ _ _ _ _ _ ν _ Z _ p L hL Φ hΦ
  haveI := secondCountable k
  haveI := t2Space k
  haveI : LocallyCompactSpace k := inferInstance
  haveI : SigmaFinite ν := inferInstance
  haveI : (Measure.pi fun _ : Fin p => ν).IsAddHaarMeasure := inferInstance
  refine map_eq_zero_of_fiber' (Measure.pi fun _ : Fin p => ν) (fun V hV => ?_) L hL Φ hΦ
  obtain ⟨s, hs⟩ := FourierPi.exists_box_subset hV
  refine ⟨boxSub (Fin p) s, ?_, ?_, ?_⟩ <;> rw [coe_boxSub]
  · exact FourierPi.isOpen_box s
  · exact FourierPi.isCompact_box s
  · exact hs

end GlobalTheory.DetEqv.Transl
