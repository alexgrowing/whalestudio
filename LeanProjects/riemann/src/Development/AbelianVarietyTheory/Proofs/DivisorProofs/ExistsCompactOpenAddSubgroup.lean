import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff

open MeasureTheory Filter Topology

namespace GlobalTheory.WeilM.HaarUniq

variable {V : Type} [AddCommGroup V] [TopologicalSpace V]

open MeasureTheory Filter Topology in
variable {V : Type} [AddCommGroup V] [TopologicalSpace V] in

theorem _root_.GlobalTheory.WeilM.HaarUniq.exists_compact_openAddSubgroup [NonarchimedeanAddGroup V]
    [LocallyCompactSpace V] :
    ∃ K : OpenAddSubgroup V, IsCompact (K : Set V) := by
  obtain ⟨C, hC, hC0⟩ := exists_compact_mem_nhds (0 : V)
  obtain ⟨K, hK⟩ := NonarchimedeanAddGroup.is_nonarchimedean C hC0
  exact ⟨K, hC.of_isClosed_subset K.isClosed hK⟩

open MeasureTheory Filter Topology in
variable {V : Type} [AddCommGroup V] [TopologicalSpace V] in

theorem _root_.GlobalTheory.WeilM.HaarUniq.indicator_mem [IsTopologicalAddGroup V] [T2Space V]
    (K : OpenAddSubgroup V) (hK : IsCompact (K : Set V)) :
    Set.indicator (K : Set V) (fun _ => (1 : ℂ)) ∈ _root_.GlobalTheory.WeilM.SB V := by
  simp only [_root_.GlobalTheory.WeilM.SB, Submodule.mem_mk,
    AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_setOf_eq]
  refine ⟨?_, HasCompactSupport.intro hK fun x hx => Set.indicator_of_notMem hx _⟩
  refine (IsLocallyConstant.iff_exists_open _).2 fun x => ?_
  by_cases hx : x ∈ (K : Set V)
  · exact ⟨K, K.isOpen, hx, fun y hy => by simp [Set.indicator_of_mem hy, Set.indicator_of_mem hx]⟩
  · exact ⟨(K : Set V)ᶜ, K.isClosed.isOpen_compl, hx, fun y hy => by
      simp [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]⟩

open MeasureTheory Filter Topology in
variable {V : Type} [AddCommGroup V] [TopologicalSpace V] in

theorem _root_.GlobalTheory.WeilM.HaarUniq.exists_invariant [NonarchimedeanAddGroup V] {φ : V → ℂ}
    (hφ : φ ∈ _root_.GlobalTheory.WeilM.SB V) :
    ∃ K : OpenAddSubgroup V, ∀ k ∈ K, ∀ x, φ (x + k) = φ x := by
  have hφ' : IsLocallyConstant φ ∧ HasCompactSupport φ := by
    simpa [_root_.GlobalTheory.WeilM.SB] using hφ
  obtain ⟨hlc, hcs⟩ := hφ'
  have hnhds : ∀ x : V, (fun w => x + w) ⁻¹' {y | φ y = φ x} ∈ 𝓝 (0 : V) := by
    intro x
    refine (continuous_const_add x).continuousAt.preimage_mem_nhds ?_
    rw [add_zero]
    exact (hlc.isOpen_fiber (φ x)).mem_nhds rfl
  choose W hW using fun x => NonarchimedeanAddGroup.is_nonarchimedean _ (hnhds x)
  have hval : ∀ i y, y - i ∈ W i → φ y = φ i := by
    intro i y hy
    have := hW i hy
    simpa using this
  obtain ⟨t, ht⟩ := hcs.isCompact.elim_finite_subcover (fun i => (fun y => y - i) ⁻¹' (W i))
    (fun i => (W i).isOpen.preimage (continuous_sub_right i))
    (fun y _ => Set.mem_iUnion.2 ⟨y, by simpa using (W y).zero_mem⟩)
  refine ⟨t.inf W, fun k hk x => ?_⟩
  have hkW : ∀ i ∈ t, k ∈ W i := fun i hi => (Finset.inf_le hi : t.inf W ≤ W i) hk
  by_cases hx : x ∈ tsupport φ
  · obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.1 (ht hx)
    have hxi' : x - i ∈ W i := hxi
    have hxk : x + k - i ∈ W i := by
      have := (W i).add_mem hxi' (hkW i hi)
      rwa [sub_add_eq_add_sub] at this
    rw [hval i _ hxk, hval i _ hxi']
  by_cases hxk : x + k ∈ tsupport φ
  · obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.1 (ht hxk)
    have hxi' : x + k - i ∈ W i := hxi
    have hx' : x - i ∈ W i := by
      have := (W i).sub_mem hxi' (hkW i hi)
      rwa [sub_right_comm, add_sub_cancel_right] at this
    rw [hval i _ hxi', hval i _ hx']
  rw [image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hxk]

open MeasureTheory Filter Topology in
variable {V : Type} [AddCommGroup V] [TopologicalSpace V] in

theorem _root_.GlobalTheory.WeilM.HaarUniq.exists_decomp [IsTopologicalAddGroup V] (K : OpenAddSubgroup V)
    {φ : V → ℂ} (hc : HasCompactSupport φ) (hinv : ∀ k ∈ K, ∀ x, φ (x + k) = φ x) :
    ∃ S : Finset (V ⧸ K.toAddSubgroup),
      φ = ∑ q ∈ S, φ q.out • (fun x => Set.indicator (K : Set V) (fun _ => (1 : ℂ)) (x + -q.out)) := by
  classical
  obtain ⟨t, ht⟩ := hc.isCompact.elim_finite_subcover (fun p : V => (fun y => -p + y) ⁻¹' (K : Set V))
    (fun p => K.isOpen.preimage (continuous_const_add (-p)))
    (fun y _ => Set.mem_iUnion.2 ⟨y, by simpa using K.zero_mem⟩)
  refine ⟨t.image (QuotientAddGroup.mk : V → V ⧸ K.toAddSubgroup), ?_⟩
  funext x
  have hmem : ∀ q : V ⧸ K.toAddSubgroup,
      (x + -q.out ∈ (K : Set V)) ↔ q = (QuotientAddGroup.mk x : V ⧸ K.toAddSubgroup) := by
    intro q
    conv_rhs => rw [← QuotientAddGroup.out_eq' q]
    rw [QuotientAddGroup.eq, add_comm]
    simp
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Set.indicator_apply, hmem,
    mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq']
  split_ifs with hS
  · have h := QuotientAddGroup.out_eq' (QuotientAddGroup.mk x : V ⧸ K.toAddSubgroup)
    rw [QuotientAddGroup.eq] at h
    have := hinv _ h ((QuotientAddGroup.mk x : V ⧸ K.toAddSubgroup).out)
    rw [add_neg_cancel_left] at this
    exact this
  · apply image_eq_zero_of_notMem_tsupport
    intro hx
    apply hS
    obtain ⟨p, hp, hxp⟩ := Set.mem_iUnion₂.1 (ht hx)
    refine Finset.mem_image.2 ⟨p, hp, ?_⟩
    rw [QuotientAddGroup.eq]
    simpa using hxp

open MeasureTheory Filter Topology in
variable {V : Type} [AddCommGroup V] [TopologicalSpace V] in
private theorem exists_coeff_form_and_integral [IsTopologicalAddGroup V] [T2Space V]
    [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure]
    (m : (V → ℂ) →ₗ[ℂ] ℂ)
    (hm : ∀ φ ∈ _root_.GlobalTheory.WeilM.SB V, ∀ a : V,
      m (fun x => φ (x + a)) = m φ)
    (H : OpenAddSubgroup V) (hH : IsCompact (H : Set V)) {φ : V → ℂ} (hc : HasCompactSupport φ)
    (hinv : ∀ k ∈ H, ∀ x, φ (x + k) = φ x) :
    ∃ A : ℂ, m φ = A * m (Set.indicator (H : Set V) (fun _ => (1 : ℂ))) ∧
      ∫ x, φ x ∂μ = A * (μ.real (H : Set V) : ℂ) := by
  obtain ⟨S, hS⟩ := _root_.GlobalTheory.WeilM.HaarUniq.exists_decomp H hc hinv
  have hmemH := _root_.GlobalTheory.WeilM.HaarUniq.indicator_mem H hH
  have hint : Integrable (Set.indicator (H : Set V) (fun _ => (1 : ℂ))) μ :=
    (integrable_indicator_iff H.isOpen.measurableSet).2 (integrableOn_const hH.measure_lt_top.ne)
  refine ⟨∑ q ∈ S, φ q.out, ?_, ?_⟩
  · calc m φ = m (∑ q ∈ S, φ q.out •
          (fun x => Set.indicator (H : Set V) (fun _ => (1 : ℂ)) (x + -q.out))) := congrArg m hS
      _ = ∑ q ∈ S, φ q.out * m (Set.indicator (H : Set V) (fun _ => (1 : ℂ))) := by
          rw [map_sum]
          refine Finset.sum_congr rfl fun q _ => ?_
          rw [map_smul, smul_eq_mul, hm _ hmemH]
      _ = _ := by rw [Finset.sum_mul]
  · calc ∫ x, φ x ∂μ = ∫ x, (∑ q ∈ S, φ q.out •
          (fun x => Set.indicator (H : Set V) (fun _ => (1 : ℂ)) (x + -q.out))) x ∂μ := by
            rw [← hS]
      _ = ∑ q ∈ S, φ q.out * (μ.real (H : Set V) : ℂ) := by
          simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
          rw [integral_finset_sum]
          · refine Finset.sum_congr rfl fun q _ => ?_
            rw [integral_const_mul,
              integral_add_right_eq_self (fun x => Set.indicator (H : Set V) (fun _ => (1 : ℂ)) x),
              integral_indicator_const _ H.isOpen.measurableSet]
            simp
          · intro q _
            exact (hint.comp_add_right _).const_mul _
      _ = _ := by rw [Finset.sum_mul]

open MeasureTheory Filter Topology in
variable {V : Type} [AddCommGroup V] [TopologicalSpace V] in

theorem _root_.GlobalTheory.WeilM.HaarUniq.exists_eq_mul_integral : ∀ (V : Type) [AddCommGroup V]
    [TopologicalSpace V] [NonarchimedeanAddGroup V]
    [LocallyCompactSpace V] [T2Space V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V)
    [μ.IsAddHaarMeasure]
    (m : (V → ℂ) →ₗ[ℂ] ℂ), (∀ φ ∈ _root_.GlobalTheory.WeilM.SB V, ∀ a : V,
      m (fun x => φ (x + a)) = m φ) →
    ∃ c : ℂ, ∀ φ ∈ _root_.GlobalTheory.WeilM.SB V, m φ = c * ∫ x, φ x ∂μ := by
  intro V _ _ _ _ _ _ _ μ _ m hm
  obtain ⟨K₀, hK₀⟩ := _root_.GlobalTheory.WeilM.HaarUniq.exists_compact_openAddSubgroup (V := V)
  have hpos : ∀ H : OpenAddSubgroup V, IsCompact (H : Set V) → μ.real (H : Set V) ≠ 0 := by
    intro H hH
    rw [measureReal_def, ENNReal.toReal_ne_zero]
    exact ⟨(H.isOpen.measure_pos μ ⟨0, H.zero_mem⟩).ne', hH.measure_lt_top.ne⟩
  refine ⟨m (Set.indicator (K₀ : Set V) (fun _ => (1 : ℂ))) / (μ.real (K₀ : Set V) : ℂ),
    fun φ hφ => ?_⟩
  have hφ' : IsLocallyConstant φ ∧ HasCompactSupport φ := by
    simpa [_root_.GlobalTheory.WeilM.SB] using hφ
  obtain ⟨K₁, hK₁⟩ := _root_.GlobalTheory.WeilM.HaarUniq.exists_invariant hφ
  set H : OpenAddSubgroup V := K₀ ⊓ K₁
  have hH : IsCompact (H : Set V) := by
    refine hK₀.of_isClosed_subset H.isClosed ?_
    rw [OpenAddSubgroup.coe_inf]
    exact Set.inter_subset_left
  have hHK₁ : ∀ k ∈ H, k ∈ K₁ := fun k hk => by
    have : k ∈ (H : Set V) := hk
    rw [OpenAddSubgroup.coe_inf] at this
    exact this.2
  have hHK₀ : ∀ k ∈ H, k ∈ K₀ := fun k hk => by
    have : k ∈ (H : Set V) := hk
    rw [OpenAddSubgroup.coe_inf] at this
    exact this.1
  obtain ⟨A, hA₁, hA₂⟩ := exists_coeff_form_and_integral μ m hm H hH hφ'.2
    (fun k hk x => hK₁ k (hHK₁ k hk) x)
  obtain ⟨B, hB₁, hB₂⟩ := exists_coeff_form_and_integral μ m hm H hH
    (φ := Set.indicator (K₀ : Set V) (fun _ => (1 : ℂ)))
    (HasCompactSupport.intro hK₀ fun x hx => Set.indicator_of_notMem hx _)
    (fun k hk x => by
      by_cases hx : x ∈ K₀ <;>
        simp [Set.indicator_apply, hx, add_mem_cancel_right (hHK₀ k hk)])
  rw [integral_indicator_const _ K₀.isOpen.measurableSet, Complex.real_smul, mul_one] at hB₂
  have hH0 : (μ.real (H : Set V) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (hpos H hH)
  have hK0 : (μ.real (K₀ : Set V) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (hpos K₀ hK₀)
  rw [hA₁, hA₂, hB₁, hB₂]
  have hB0 : B ≠ 0 := by
    rintro rfl
    apply hK0
    rw [hB₂, zero_mul]
  field_simp

end GlobalTheory.WeilM.HaarUniq
