import Mathlib
import Formalism.PeriodIntegrals.WeilQuotMeas
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilQuotientMeasure.StepBruhat

noncomputable section

open MeasureTheory Topology
open scoped ENNReal Pointwise

namespace PI.WeilQuotMeas.UnitaryGroupMassFormula

section Lemmas

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] {H : Subgroup G}

theorem measurable_mul_coe : Measurable (fun p : G × H => p.1 * (p.2 : G)) := measurable_fst.mul (measurable_subtype_coe.comp measurable_snd)

theorem measurable_avg (ν : Measure H) [SFinite ν] {f : G → ℝ≥0∞} (hf : Measurable f) :
    Measurable (fun g : G => ∫⁻ h, f (g * (h : G)) ∂ν) := (hf.comp measurable_mul_coe).lintegral_prod_right'

theorem avg_mul_right (ν : Measure H) [ν.IsMulLeftInvariant] (f : G → ℝ≥0∞) (g : G) (k : H) :
    ∫⁻ h, f (g * (k : G) * (h : G)) ∂ν = ∫⁻ h, f (g * (h : G)) ∂ν := by
  have e := lintegral_mul_left_eq_self (μ := ν) (fun h : H => f (g * (h : G))) k
  simpa [mul_assoc] using e

theorem lintegral_mul_avg_comm (μ : Measure G) (ν : Measure H) [SFinite μ] [SFinite ν]
    [μ.IsMulRightInvariant] [ν.IsInvInvariant] {f β : G → ℝ≥0∞} (hf : Measurable f)
    (hβ : Measurable β) :
    ∫⁻ g, f g * ∫⁻ h, β (g * (h : G)) ∂ν ∂μ = ∫⁻ g, β g * ∫⁻ h, f (g * (h : G)) ∂ν ∂μ := by
  calc ∫⁻ g, f g * ∫⁻ h, β (g * (h : G)) ∂ν ∂μ
      = ∫⁻ g, ∫⁻ h, f g * β (g * (h : G)) ∂ν ∂μ := by
        refine lintegral_congr fun g => ?_
        rw [lintegral_const_mul]
        exact hβ.comp (measurable_const.mul measurable_subtype_coe)
    _ = ∫⁻ h, ∫⁻ g, f g * β (g * (h : G)) ∂μ ∂ν :=
        lintegral_lintegral_swap ((hf.comp measurable_fst).mul (hβ.comp measurable_mul_coe)).aemeasurable
    _ = ∫⁻ h, ∫⁻ g, f (g * ((h : G))⁻¹) * β g ∂μ ∂ν := by
        refine lintegral_congr fun h => ?_
        have e := lintegral_mul_right_eq_self (μ := μ) (fun x => f (x * ((h : G))⁻¹) * β x) (h : G)
        simp only [mul_inv_cancel_right] at e
        exact e
    _ = ∫⁻ g, ∫⁻ h, f (g * ((h : G))⁻¹) * β g ∂ν ∂μ :=
        lintegral_lintegral_swap ((hf.comp (measurable_snd.mul
          (measurable_subtype_coe.comp measurable_fst).inv)).mul (hβ.comp measurable_snd)).aemeasurable
    _ = ∫⁻ g, β g * ∫⁻ h, f (g * (h : G)) ∂ν ∂μ := by
        refine lintegral_congr fun g => ?_
        have e := lintegral_inv_eq_self (μ := ν) (fun h : H => f (g * (h : G)))
        simp only [InvMemClass.coe_inv] at e
        rw [lintegral_mul_const, e]
        · exact mul_comm _ _
        · exact hf.comp (measurable_const.mul measurable_subtype_coe.inv)

theorem exists_compact_lift (K : Set (G ⧸ H)) (hK : IsCompact K) :
    ∃ C : Set G, IsCompact C ∧ K ⊆ (QuotientGroup.mk : G → G ⧸ H) '' C := by
  have hopen : IsOpenMap (QuotientGroup.mk : G → G ⧸ H) := QuotientGroup.isOpenMap_coe
  choose V hVc hxV using fun x : G => exists_compact_mem_nhds x
  have hcov : K ⊆ ⋃ x : G, (QuotientGroup.mk : G → G ⧸ H) '' interior (V x) := by
    intro y _
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    exact Set.mem_iUnion.2 ⟨x, x, mem_interior_iff_mem_nhds.2 (hxV x), rfl⟩
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover _ (fun x => hopen _ isOpen_interior) hcov
  refine ⟨⋃ x ∈ s, V x, s.isCompact_biUnion fun x _ => hVc x, hs.trans ?_⟩
  simp only [Set.iUnion_subset_iff]
  intro x hx
  refine Set.image_mono (interior_subset.trans ?_)
  intro z hz
  exact Set.mem_iUnion₂.2 ⟨x, hx, hz⟩

end Lemmas

theorem weilQuotient_of_parts (hb : StepBruhat) (hi : StepInvInv) (h2 : WqUnique) :
    WeilQuotient := by
  unfold StepBruhat StepInvInv WqUnique at *
  unfold WeilQuotient
  intro G _ _ _ _ _ _ _ _ H hH μ ν hμ hμr hν hνr
  haveI : LocallyCompactSpace H := hH.locallyCompactSpace
  haveI : SecondCountableTopology H := TopologicalSpace.Subtype.secondCountableTopology (H : Set G)
  haveI hνi : ν.IsInvInvariant := hi H ν hν hνr
  obtain ⟨β, hβm, hβ1⟩ := hb G H hH ν hν
  have hmk : Measurable (QuotientGroup.mk : G → G ⧸ H) := QuotientGroup.measurable_coe
  obtain ⟨ρ, hρdef⟩ : ∃ ρ : Measure (G ⧸ H), ρ = Measure.map QuotientGroup.mk (μ.withDensity β) :=
    ⟨_, rfl⟩
  have hρ : ∀ F : G ⧸ H → ℝ≥0∞, Measurable F →
      ∫⁻ y, F y ∂ρ = ∫⁻ g, β g * F (g : G ⧸ H) ∂μ := by
    intro F hF
    rw [hρdef, lintegral_map hF hmk]
    exact lintegral_withDensity_eq_lintegral_mul _ hβm (hF.comp hmk)
  have hout : ∀ (f : G → ℝ≥0∞) (g : G),
      ∫⁻ h, f (Quotient.out (g : G ⧸ H) * (h : G)) ∂ν = ∫⁻ h, f (g * (h : G)) ∂ν := by
    intro f g
    have e : ((Quotient.out (g : G ⧸ H) : G) : G ⧸ H) = (g : G ⧸ H) := Quotient.out_eq _
    rw [QuotientGroup.eq] at e
    have hk : Quotient.out (g : G ⧸ H) = g * ((Quotient.out (g : G ⧸ H))⁻¹ * g)⁻¹ := by group
    rw [hk]
    exact avg_mul_right ν f g ⟨_, H.inv_mem e⟩
  have hΦm : ∀ f : G → ℝ≥0∞, Measurable f →
      Measurable (fun y : G ⧸ H => ∫⁻ h, f (Quotient.out y * (h : G)) ∂ν) := by
    intro f hf
    refine measurable_from_quotient.2 ?_
    convert measurable_avg ν hf using 1
    funext g
    exact hout f g
  have hunf : ∀ f : G → ℝ≥0∞, Measurable f →
      ∫⁻ g, f g ∂μ = ∫⁻ y, ∫⁻ h, f (Quotient.out y * (h : G)) ∂ν ∂ρ := by
    intro f hf
    rw [hρ _ (hΦm f hf)]
    simp_rw [hout f]
    rw [lintegral_mul_avg_comm μ ν hβm hf]
    simp [hβ1]
  have hne : ρ ≠ 0 := by
    intro h0
    have e := hunf (fun _ => 1) measurable_const
    simp only [h0, lintegral_zero_measure, lintegral_const, one_mul,
      Measure.measure_univ_eq_zero] at e
    simp at e
    exact NeZero.ne μ e
  have hfin : ∀ K : Set (G ⧸ H), IsCompact K → ρ K < ∞ := by
    intro K hK
    obtain ⟨C, hC, hKC⟩ := exists_compact_lift K hK
    obtain ⟨U, hUc, hU1⟩ := exists_compact_mem_nhds (1 : G)
    have hD : IsCompact (C * U) := hC.mul hUc
    have hf : Measurable ((C * U).indicator (1 : G → ℝ≥0∞)) :=
      measurable_one.indicator hD.measurableSet
    have hUm : MeasurableSet (Subtype.val ⁻¹' U : Set H) :=
      measurable_subtype_coe hUc.measurableSet
    have hδ : ν (Subtype.val ⁻¹' U : Set H) ≠ 0 := by
      have ho : IsOpen (Subtype.val ⁻¹' interior U : Set H) :=
        isOpen_interior.preimage continuous_subtype_val
      have hne' : (Subtype.val ⁻¹' interior U : Set H).Nonempty :=
        ⟨1, mem_interior_iff_mem_nhds.2 hU1⟩
      exact ((ho.measure_pos ν hne').trans_le
        (measure_mono (Set.preimage_mono interior_subset))).ne'
    have key : ∀ y ∈ K, ν (Subtype.val ⁻¹' U : Set H) ≤
        ∫⁻ h, (C * U).indicator (1 : G → ℝ≥0∞) (Quotient.out y * (h : G)) ∂ν := by
      intro y hy
      obtain ⟨c, hc, rfl⟩ := hKC hy
      rw [hout _ c, ← lintegral_indicator_one hUm]
      refine lintegral_mono fun h => ?_
      by_cases hh : (h : G) ∈ U
      · have hm : c * (h : G) ∈ C * U := Set.mul_mem_mul hc hh
        rw [Set.indicator_of_mem (show h ∈ (Subtype.val ⁻¹' U : Set H) from hh),
          Set.indicator_of_mem hm]
        exact le_rfl
      · rw [Set.indicator_of_notMem (show h ∉ (Subtype.val ⁻¹' U : Set H) from hh)]
        exact zero_le
    have hle : ν (Subtype.val ⁻¹' U : Set H) * ρ K ≤ μ (C * U) := by
      calc ν (Subtype.val ⁻¹' U : Set H) * ρ K
          ≤ ν (Subtype.val ⁻¹' U : Set H) * ρ {y | ν (Subtype.val ⁻¹' U : Set H) ≤
              ∫⁻ h, (C * U).indicator (1 : G → ℝ≥0∞) (Quotient.out y * (h : G)) ∂ν} :=
            mul_le_mul_of_nonneg_left (measure_mono fun y hy => key y hy) (zero_le)
        _ ≤ ∫⁻ y, ∫⁻ h, (C * U).indicator (1 : G → ℝ≥0∞) (Quotient.out y * (h : G)) ∂ν ∂ρ :=
            mul_meas_ge_le_lintegral₀ (hΦm _ hf).aemeasurable _
        _ = ∫⁻ g, (C * U).indicator (1 : G → ℝ≥0∞) g ∂μ := (hunf _ hf).symm
        _ = μ (C * U) := lintegral_indicator_one hD.measurableSet
    rw [lt_top_iff_ne_top]
    intro htop
    rw [htop, ENNReal.mul_top hδ] at hle
    exact hD.measure_lt_top.ne (top_le_iff.1 hle)
  have hswap : ∀ β₁ β₂ : G → ℝ≥0∞, Measurable β₁ → Measurable β₂ →
      (∀ x, ∫⁻ h, β₁ (x * (h : G)) ∂ν = 1) → (∀ x, ∫⁻ h, β₂ (x * (h : G)) ∂ν = 1) →
      ∀ ψ : G ⧸ H → ℝ≥0∞, Measurable ψ →
        ∫⁻ x, β₁ x * ψ (x : G ⧸ H) ∂μ = ∫⁻ x, β₂ x * ψ (x : G ⧸ H) ∂μ := by
    intro β₁ β₂ m1 m2 n1 n2 ψ hψ
    have hf : Measurable (fun x => β₁ x * ψ (x : G ⧸ H)) := m1.mul (hψ.comp hmk)
    have e := lintegral_mul_avg_comm μ ν hf m2
    simp only [n2, mul_one] at e
    rw [e]
    refine lintegral_congr fun x => ?_
    have hc : ∀ h : H, ψ ((x * (h : G) : G) : G ⧸ H) = ψ (x : G ⧸ H) := fun h => by
      rw [QuotientGroup.mk_mul_of_mem x h.2]
    simp_rw [hc]
    rw [lintegral_mul_const, n1, one_mul]
    exact m1.comp (measurable_const.mul measurable_subtype_coe)
  have hinv : ∀ (g : G) (s : Set (G ⧸ H)), MeasurableSet s →
      ρ ((fun y => g • y) ⁻¹' s) = ρ s := by
    intro g s hs
    have hsm : Measurable (fun y : G ⧸ H => g • y) :=
      measurable_from_quotient.2 (hmk.comp (measurable_const_mul g))
    have hpre : MeasurableSet ((fun y : G ⧸ H => g • y) ⁻¹' s) := hsm hs
    have hψ : Measurable (s.indicator (1 : G ⧸ H → ℝ≥0∞)) := measurable_one.indicator hs
    rw [← lintegral_indicator_one hpre, ← lintegral_indicator_one hs,
      hρ _ (measurable_one.indicator hpre), hρ _ hψ]
    have e1 : ∀ x : G, ((fun y : G ⧸ H => g • y) ⁻¹' s).indicator (1 : G ⧸ H → ℝ≥0∞) (x : G ⧸ H) =
        s.indicator 1 ((g * x : G) : G ⧸ H) := fun x => rfl
    simp_rw [e1]
    have e2 := lintegral_mul_left_eq_self (μ := μ)
      (fun x => β (g⁻¹ * x) * s.indicator (1 : G ⧸ H → ℝ≥0∞) (x : G ⧸ H)) g
    simp only [inv_mul_cancel_left] at e2
    rw [e2]
    exact hswap (fun x => β (g⁻¹ * x)) β (hβm.comp (measurable_const_mul _)) hβm
      (fun x => by simpa [mul_assoc] using hβ1 (g⁻¹ * x)) hβ1 _ hψ
  exact ⟨ρ, hne, hfin, hinv, hunf, fun ρ' a b => h2 G H hH ρ ρ' hne hfin hinv a b⟩

end PI.WeilQuotMeas.UnitaryGroupMassFormula
