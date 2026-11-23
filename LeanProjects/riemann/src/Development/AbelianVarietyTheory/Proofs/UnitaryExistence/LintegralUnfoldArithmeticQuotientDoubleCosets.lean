import Mathlib
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsStrictMeasurableFundamentalSetOfDiscrete
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MapRestrictSubgroupEqCommonSmulHaar

open MeasureTheory Topology Matrix
open scoped ENNReal

namespace GlobalTheory.PeterssonUnfold

theorem unfold_lintegral :
    ∀ (G : Type) [Group G] [MeasurableSpace G] [MeasurableMul G] (μ : Measure G) [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] (Γ H Kf : Subgroup G) [Countable Γ] (𝓕 : Set G), IsFundamentalDomain Γ 𝓕 μ → μ 𝓕 ≠ 0 → μ 𝓕 ≠ ⊤ → MeasurableSet (H : Set G) → Kf ≤ H → ∀ (ι : Type) [Fintype ι] (R : ι → Type) [∀ k, Group (R k)] [∀ k, TopologicalSpace (R k)] [∀ k, IsTopologicalGroup (R k)] [∀ k, T2Space (R k)] [∀ k, LocallyCompactSpace (R k)] [∀ k, SecondCountableTopology (R k)] [∀ k, MeasurableSpace (R k)] [∀ k, BorelSpace (R k)] (ν : ∀ k, Measure (R k)) [∀ k, (ν k).IsHaarMeasure] (ψ : ∀ k, G →* R k) (Λ : ∀ k, Subgroup (R k)) (s : ∀ k, R k) (g : ι → G) (P : Type) (Q : P → P → Prop) (dict : G → P) (pt : ∀ k, R k → P), (∀ k, Measurable (ψ k)) → (∀ k t, ∃ h ∈ H, ψ k h = t) → (∀ k, ∀ z ∈ Kf, ψ k z = 1) → (∀ k, ∀ γ ∈ Γ, ψ k γ = 1 → γ = 1) → (∀ k k', ∃ (e : R k ≃ᵐ R k') (α : R k → R k) (u : R k), MeasurePreserving e (ν k) (ν k') ∧ Measurable α ∧ (∀ x, ψ k' x = e (α (ψ k x))) ∧ ∀ t, α (α t) = u⁻¹ * t * u) → (∀ k, ∃ W ∈ 𝓝 (1 : R k), ∀ w ∈ Λ k, w ∈ W → w = 1) → Equivalence Q → (∀ x x', Q (dict x) (dict x') ↔ ∃ γ ∈ Γ, ∃ z ∈ Kf, x' = γ * x * z) → (∀ k, ∀ h ∈ H, Q (dict (g k * h)) (pt k (s k * ψ k h))) → (∀ x, ∃ k t, Q (dict x) (pt k t)) → (∀ k k' t t', Q (pt k t) (pt k' t') → k = k') → (∀ k t t', Q (pt k t) (pt k t') ↔ ∃ w ∈ Λ k, t' = w * t) → ∃ (κ : ℝ≥0∞) (D : ∀ k, Set (R k)), κ ≠ 0 ∧ κ ≠ ⊤ ∧ (∀ k, Countable (Λ k) ∧ IsFundamentalDomain (Λ k) (D k) (ν k)) ∧ ∀ Φ : P → ℝ≥0∞, (∀ x q, Q (dict x) q → Φ q = Φ (dict x)) → (∀ k, Measurable fun t => Φ (pt k t)) → Measurable (fun x => Φ (dict x)) ∧ ∫⁻ x in 𝓕, Φ (dict x) ∂μ = κ * ∑ k, ∫⁻ t in D k, Φ (pt k t) ∂(ν k) := by
  classical
  intro G _ _ _ μ _ _ Γ H Kf _ 𝓕 h𝓕 h0 htop hH hKH ι _ R _ _ _ _ _ _ _ _ ν _ ψ Λ s g P Q dict pt
    hψ hsurj hK hΓ hcomp hdisc hQ hdict hpt hcov hsep hΛ
  have hD := fun k => GlobalTheory.exists_strict_measurable_fundamental_set_of_discrete (R k) (Λ k) (hdisc k)
  have hcount : ∀ k, Countable (Λ k) := fun k => (hD k).1
  choose D hDm hDu using fun k => (hD k).2
  have hpt' : ∀ k y, (g k)⁻¹ * y ∈ H → Q (dict y) (pt k (s k * ψ k ((g k)⁻¹ * y))) := by
    intro k y hy
    have := hpt k _ hy
    rwa [mul_inv_cancel_left] at this
  have hΓQ : ∀ δ ∈ Γ, ∀ y, Q (dict y) (dict (δ * y)) := fun δ hδ y =>
    (hdict _ _).2 ⟨δ, hδ, 1, Kf.one_mem, by rw [mul_one]⟩
  have inj1 : ∀ k k' y, ∀ δ ∈ Γ, (g k)⁻¹ * y ∈ H → (g k')⁻¹ * (δ * y) ∈ H →
      Q (pt k (s k * ψ k ((g k)⁻¹ * y))) (pt k' (s k' * ψ k' ((g k')⁻¹ * (δ * y)))) :=
    fun k k' y δ hδ hy hy' =>
      hQ.trans (hQ.symm (hpt' k y hy)) (hQ.trans (hΓQ δ hδ y) (hpt' k' _ hy'))
  have inj2 : ∀ k y, ∀ δ ∈ Γ, (g k)⁻¹ * y ∈ H → (g k)⁻¹ * (δ * y) ∈ H →
      ∃ w ∈ Λ k, s k * ψ k ((g k)⁻¹ * (δ * y)) = w * (s k * ψ k ((g k)⁻¹ * y)) ∧
        (w = 1 → δ = 1) := by
    intro k y δ hδ hy hy'
    obtain ⟨w, hw, he⟩ := (hΛ k _ _).1 (inj1 k k y δ hδ hy hy')
    refine ⟨w, hw, he, fun h1 => hΓ k δ hδ ?_⟩
    rw [h1, one_mul, mul_right_inj, map_mul, map_mul, map_mul, mul_right_inj] at he
    exact mul_eq_right.1 he
  let E : ι → Set G := fun k => {y | (g k)⁻¹ * y ∈ H ∧ s k * ψ k ((g k)⁻¹ * y) ∈ D k}
  have hms : ∀ k, Measurable fun y : G => s k * ψ k ((g k)⁻¹ * y) := fun k =>
    ((hψ k).comp (measurable_const_mul _)).const_mul _
  have hEm : ∀ k, MeasurableSet (E k) := fun k =>
    (measurable_const_mul (g k)⁻¹ hH).inter (hms k (hDm k))
  have cover : ∀ x, ∃ γ ∈ Γ, ∃ k, γ * x ∈ E k := by
    intro x
    obtain ⟨k, t, hq⟩ := hcov x
    obtain ⟨w, hw, -⟩ := hDu k t
    obtain ⟨h, hh, he⟩ := hsurj k ((s k)⁻¹ * (w * t))
    have h1 : Q (pt k t) (pt k (s k * ψ k h)) :=
      (hΛ k _ _).2 ⟨w, w.2, by rw [he, mul_inv_cancel_left]⟩
    obtain ⟨γ, hγ, z, hz, hx⟩ := (hdict x (g k * h)).1
      (hQ.trans hq (hQ.trans h1 (hQ.symm (hpt k h hh))))
    have h2 : (g k)⁻¹ * (γ * x) = h * z⁻¹ := by
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hx, mul_inv_cancel_right]
    refine ⟨γ, hγ, k, ?_, ?_⟩
    · rw [h2]; exact H.mul_mem hh (H.inv_mem (hKH hz))
    · rw [h2, map_mul, map_inv, hK k z hz, inv_one, mul_one, he, mul_inv_cancel_left]
      exact hw
  have uniq : ∀ k k' y, ∀ δ ∈ Γ, y ∈ E k → δ * y ∈ E k' → k = k' ∧ δ = 1 := by
    intro k k' y δ hδ hy hy'
    obtain rfl : k = k' := hsep _ _ _ _ (inj1 k k' y δ hδ hy.1 hy'.1)
    refine ⟨rfl, ?_⟩
    obtain ⟨w, hw, he, h1⟩ := inj2 k y δ hδ hy.1 hy'.1
    refine h1 ?_
    have := (hDu k (s k * ψ k ((g k)⁻¹ * y))).unique (y₁ := ⟨w, hw⟩) (y₂ := 1)
      (by have := hy'.2; rwa [he] at this) (by simpa using hy.2)
    exact congrArg Subtype.val this
  have hE : IsFundamentalDomain Γ (⋃ k, E k) μ := by
    refine IsFundamentalDomain.mk' (MeasurableSet.iUnion hEm).nullMeasurableSet fun x => ?_
    obtain ⟨γ, hγ, k, hx⟩ := cover x
    refine ⟨⟨γ, hγ⟩, Set.mem_iUnion.2 ⟨k, hx⟩, fun γ' hγ' => ?_⟩
    obtain ⟨k', hx'⟩ := Set.mem_iUnion.1 hγ'
    have := (uniq k k' (γ * x) (γ' * γ⁻¹) (Γ.mul_mem γ'.2 (Γ.inv_mem hγ)) hx
      (by rw [mul_assoc, inv_mul_cancel_left]; exact hx')).2
    exact Subtype.ext (mul_inv_eq_one.1 this)
  have hH0 : μ H ≠ 0 := by
    intro hH0
    apply h0
    rw [h𝓕.measure_eq hE]
    refine measure_iUnion_null fun k => measure_mono_null (t := (fun y => (g k)⁻¹ * y) ⁻¹' H)
      (fun y hy => hy.1) ?_
    rw [measure_preimage_mul, hH0]
  have hloc : ∀ k t, ∃ W ∈ 𝓝 t, μ ((H : Set G) ∩ ψ k ⁻¹' W) ≠ ⊤ := by
    intro k t
    obtain ⟨U, hU, hΛU⟩ := hdisc k
    obtain ⟨V₀, hV₀, hVU⟩ := exists_nhds_split_inv hU
    obtain ⟨V, hVV, hVo, hV1⟩ := mem_nhds_iff.1 hV₀
    have ho : IsOpen {u : R k | s k * u * (s k * t)⁻¹ ∈ V} := hVo.preimage (by fun_prop)
    refine ⟨_, ho.mem_nhds (by simpa using hV1), fun hinf => ?_⟩
    rw [← measure_preimage_mul μ (g k)⁻¹] at hinf
    obtain ⟨x, hx, y, hy, δ, hδ, hxy⟩ := h𝓕.exists_ne_one_smul_eq
      (measurable_const_mul (g k)⁻¹ (hH.inter (hψ k ho.measurableSet))).nullMeasurableSet
      (by rw [hinf]; exact lt_top_iff_ne_top.2 htop)
    subst hxy
    obtain ⟨w, hw, he, h1⟩ := inj2 k x δ δ.2 hx.1 hy.1
    refine hδ (Subtype.ext (h1 (hΛU w hw ?_)))
    have h2 : s k * ψ k ((g k)⁻¹ * (δ * x)) * (s k * t)⁻¹ ∈ V := hy.2
    have h3 : s k * ψ k ((g k)⁻¹ * x) * (s k * t)⁻¹ ∈ V := hx.2
    rw [he, mul_assoc] at h2
    have := hVU _ (hVV h2) _ (hVV h3)
    rwa [mul_div_cancel_right] at this
  obtain ⟨κ, hκ0, hκt, hκ⟩ := GlobalTheory.map_restrict_subgroup_eq_common_smul_haar G μ H hH hH0 ι R ν ψ hψ hsurj hloc hcomp
  refine ⟨κ, D, hκ0, hκt, fun k => ⟨hcount k,
    IsFundamentalDomain.mk' (hDm k).nullMeasurableSet (hDu k)⟩, fun Φ hΦ hΦm => ?_⟩
  have hinv : ∀ δ ∈ Γ, ∀ y, Φ (dict (δ * y)) = Φ (dict y) := fun δ hδ y => hΦ _ _ (hΓQ δ hδ y)
  have hval : ∀ k y, (g k)⁻¹ * y ∈ H → Φ (dict y) = Φ (pt k (s k * ψ k ((g k)⁻¹ * y))) :=
    fun k y hy => (hΦ _ _ (hpt' k y hy)).symm
  refine ⟨fun B hB => ?_, ?_⟩
  · have : (fun x => Φ (dict x)) ⁻¹' B = ⋃ γ : Γ, ⋃ k, (fun x => (γ : G) * x) ⁻¹'
        (((fun y => (g k)⁻¹ * y) ⁻¹' H) ∩
          (fun y => Φ (pt k (s k * ψ k ((g k)⁻¹ * y)))) ⁻¹' B) := by
      ext x
      simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff]
      constructor
      · intro hx
        obtain ⟨γ, hγ, k, hk⟩ := cover x
        refine ⟨⟨γ, hγ⟩, k, hk.1, ?_⟩
        rw [← hval k _ hk.1, hinv γ hγ]; exact hx
      · rintro ⟨γ, k, hk, hx⟩
        rwa [← hval k _ hk, hinv γ γ.2] at hx
    rw [this]
    exact MeasurableSet.iUnion fun γ => MeasurableSet.iUnion fun k => measurable_const_mul _
      ((measurable_const_mul _ hH).inter (((hΦm k).comp (hms k)) hB))
  · rw [h𝓕.setLIntegral_eq hE _ fun γ x => hinv γ γ.2 x,
      lintegral_iUnion hEm (fun k k' hk => Set.disjoint_left.2 fun y hy hy' =>
        hk (uniq k k' y 1 Γ.one_mem hy (by rwa [one_mul])).1), tsum_fintype, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    let F : R k → ℝ≥0∞ := (D k).indicator fun t => Φ (pt k t)
    have hF : Measurable F := (hΦm k).indicator (hDm k)
    calc ∫⁻ x in E k, Φ (dict x) ∂μ
        = ∫⁻ x, (H : Set G).indicator (fun h => F (s k * ψ k h)) ((g k)⁻¹ * x) ∂μ := by
          rw [← lintegral_indicator (hEm k)]
          refine lintegral_congr fun x => ?_
          by_cases hx : (g k)⁻¹ * x ∈ H
          · rw [Set.indicator_of_mem (s := (H : Set G)) hx]
            by_cases hx' : s k * ψ k ((g k)⁻¹ * x) ∈ D k
            · rw [Set.indicator_of_mem (show x ∈ E k from ⟨hx, hx'⟩), hval k x hx]
              exact (Set.indicator_of_mem hx' fun t => Φ (pt k t)).symm
            · rw [Set.indicator_of_notMem (fun h : x ∈ E k => hx' h.2)]
              exact (Set.indicator_of_notMem hx' fun t => Φ (pt k t)).symm
          · rw [Set.indicator_of_notMem (fun h : x ∈ E k => hx h.1),
              Set.indicator_of_notMem (s := (H : Set G)) hx]
      _ = ∫⁻ h in (H : Set G), F (s k * ψ k h) ∂μ := by
          rw [lintegral_mul_left_eq_self
            ((H : Set G).indicator (fun h => F (s k * ψ k h))) (g k)⁻¹, lintegral_indicator hH]
      _ = ∫⁻ t, F (s k * t) ∂((μ.restrict H).map (ψ k)) :=
          (lintegral_map (f := fun t => F (s k * t)) (hF.comp (measurable_const_mul _)) (hψ k)).symm
      _ = κ * ∫⁻ t in D k, Φ (pt k t) ∂(ν k) := by
          rw [hκ, lintegral_smul_measure, lintegral_mul_left_eq_self F, lintegral_indicator (hDm k),
            smul_eq_mul]

end GlobalTheory.PeterssonUnfold
