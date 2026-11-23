import Mathlib

open MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal

namespace GlobalTheory.UnipAvg

theorem tsum_eq_tsum_quotient {A : Type*} [Group A] (S : Subgroup A) (f : A → ℝ≥0∞) :
    ∑' a, f a = ∑' q : A ⧸ S, ∑' s : S, f (q.out * s) := by
  have key : ∀ (q : A ⧸ S) (s : S), (QuotientGroup.mk (q.out * s) : A ⧸ S) = q := fun q s => by
    rw [QuotientGroup.mk_mul_of_mem _ s.2, QuotientGroup.out_eq']
  let e : (A ⧸ S) × S → A := fun p => p.1.out * p.2
  have he : Function.Bijective e := by
    constructor
    · rintro ⟨q, s⟩ ⟨q', s'⟩ h
      simp only [e] at h
      have hq : q = q' := by rw [← key q s, ← key q' s', h]
      subst hq
      simp only [Prod.mk.injEq, true_and]
      exact Subtype.ext (mul_left_cancel h)
    · intro a
      refine ⟨(QuotientGroup.mk a, ⟨(QuotientGroup.mk a : A ⧸ S).out⁻¹ * a, ?_⟩), ?_⟩
      · exact QuotientGroup.eq.1 (QuotientGroup.out_eq' _)
      · simp [e]
  rw [← (Equiv.ofBijective e he).tsum_eq]
  exact ENNReal.tsum_prod (f := fun (q : A ⧸ S) (s : S) => f (q.out * s))

section Unimodular

variable {U : Type*} [Group U] [MeasurableSpace U] [MeasurableMul₂ U] [MeasurableInv U]

theorem isMulRightInvariant_of_covolume_one (ν : Measure U) [SigmaFinite ν] [ν.IsMulLeftInvariant]
    (U₀ : Subgroup U) [Countable U₀] {D : Set U} (hD : IsFundamentalDomain U₀ D ν) (hνD : ν D = 1) :
    ν.IsMulRightInvariant := by
  haveI : SMulInvariantMeasure U₀ U ν := ⟨fun γ s _ => measure_preimage_mul ν (γ : U) s⟩
  refine ⟨fun u => ?_⟩
  have hD' : IsFundamentalDomain U₀ ((· * u) ⁻¹' D) ν :=
    hD.preimage_of_equiv (quasiMeasurePreserving_mul_right ν u) (e := id) Function.bijective_id
      (fun g x => mul_assoc (g : U) x u)
  have h1 : (ν.map (· * u)) D = 1 := by
    have := (MeasurableEquiv.mulRight u).map_apply (μ := ν) D
    simp only [MeasurableEquiv.coe_mulRight] at this
    rw [this, hD'.measure_eq hD, hνD]
  haveI : SigmaFinite (ν.map (· * u)) := (MeasurableEquiv.mulRight u).sigmaFinite_map
  have h := measure_eq_div_smul (ν.map (· * u)) ν (s := D) (by rw [hνD]; exact one_ne_zero)
    (by rw [hνD]; exact ENNReal.one_ne_top)
  rw [h, h1, hνD]; simp

theorem isInvInvariant_of_covolume_one (ν : Measure U) [SigmaFinite ν] [ν.IsMulLeftInvariant]
    (U₀ : Subgroup U) [Countable U₀] {D : Set U} (hD : IsFundamentalDomain U₀ D ν) (hνD : ν D = 1) :
    ν.IsInvInvariant := by
  haveI := isMulRightInvariant_of_covolume_one ν U₀ hD hνD
  have h := measure_eq_div_smul ν.inv ν (s := D) (by rw [hνD]; exact one_ne_zero)
    (by rw [hνD]; exact ENNReal.one_ne_top)
  rw [hνD, div_one] at h
  set c := ν.inv D with hc
  have h2 : ν = (c * c) • ν := by
    calc ν = ν.inv.inv := (Measure.inv_inv ν).symm
      _ = (c • ν).inv := by rw [← h]
      _ = c • ν.inv := by simp only [Measure.inv, Measure.map_smul]
      _ = (c * c) • ν := by rw [h, smul_smul]
  have h3 : c * c = 1 := by
    have := congrArg (fun m : Measure U => m D) h2
    simpa [hνD] using this.symm
  have h4 : c = 1 := by
    rcases lt_trichotomy c 1 with hlt | heq | hgt
    · have : c * c < 1 := lt_of_le_of_lt (by simpa using mul_le_mul_right hlt.le c) hlt
      exact absurd h3 this.ne
    · exact heq
    · have : 1 < c * c := lt_of_lt_of_le hgt (by simpa using mul_le_mul_right hgt.le c)
      exact absurd h3 this.ne'
  exact ⟨by rw [h, h4, one_smul]⟩

omit [MeasurableInv U] in

theorem tsum_setLIntegral_eq_index (ν : Measure U) [ν.IsMulLeftInvariant]
    (U₀ L : Subgroup U) [Countable U₀] (hle : U₀ ≤ L) {D : Set U} (hD : IsFundamentalDomain U₀ D ν)
    (ψ : U → ℝ≥0∞) :
    ∑' l : L, ∫⁻ u in D, ψ (l * u) ∂ν = ∑' _q : L ⧸ U₀.subgroupOf L, ∫⁻ u, ψ u ∂ν := by
  haveI : SMulInvariantMeasure U₀ U ν := ⟨fun γ s _ => measure_preimage_mul ν (γ : U) s⟩
  rw [tsum_eq_tsum_quotient (U₀.subgroupOf L)]
  refine tsum_congr fun q => ?_
  rw [← lintegral_mul_left_eq_self ψ ((q.out : L) : U), hD.lintegral_eq_tsum'',
    ← (Subgroup.subgroupOfEquivOfLe hle).toEquiv.tsum_eq]
  refine tsum_congr fun b => lintegral_congr fun u => ?_
  congr 1
  exact mul_assoc _ _ _

end Unimodular

section Average

variable {G U : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
  [Group U] [MeasurableSpace U] [MeasurableMul₂ U] [MeasurableInv U]

omit [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G] [MeasurableInv U] in

theorem tsum_setLIntegral_eq_cosets (ι : U →* G) (hι : Function.Injective ι) (ν : Measure U) [ν.IsMulLeftInvariant]
    (Γ : Subgroup G) (U₀ : Subgroup U) [Countable U₀] (hle : U₀ ≤ Γ.comap ι) {D : Set U}
    (hD : IsFundamentalDomain U₀ D ν) (φ : G → ℝ≥0∞) :
    ∑' γ : Γ, ∫⁻ u in D, φ (γ * ι u) ∂ν =
      ∑' q : Γ ⧸ ι.range.subgroupOf Γ, ∑' _k : Γ.comap ι ⧸ U₀.subgroupOf (Γ.comap ι),
        ∫⁻ u, φ ((q.out : Γ) * ι u) ∂ν := by
  rw [tsum_eq_tsum_quotient (ι.range.subgroupOf Γ)]
  refine tsum_congr fun q => ?_
  rw [← tsum_setLIntegral_eq_index ν U₀ _ hle hD (fun u => φ ((q.out : Γ) * ι u))]
  let e : Γ.comap ι → ι.range.subgroupOf Γ := fun l => ⟨⟨ι l, l.2⟩, ⟨l, rfl⟩⟩
  have he : Function.Bijective e := by
    constructor
    · intro l l' h
      exact Subtype.ext (hι (congrArg (fun s : ι.range.subgroupOf Γ => ((s : Γ) : G)) h))
    · rintro ⟨⟨γ, hγ⟩, ⟨l, hl⟩⟩
      have hl' : ι l = γ := hl
      subst hl'
      exact ⟨⟨l, hγ⟩, rfl⟩
  rw [← (Equiv.ofBijective e he).tsum_eq]
  refine tsum_congr fun l => lintegral_congr fun u => ?_
  simp [e, mul_assoc]

theorem tsum_setLIntegral_inv (ι : U →* G) (hι : Function.Injective ι) (hιm : Measurable ι) (ν : Measure U)
    [ν.IsMulLeftInvariant] [ν.IsInvInvariant]
    (Γ : Subgroup G) (U₀ : Subgroup U) [Countable U₀] (hle : U₀ ≤ Γ.comap ι) {D : Set U}
    (hD : IsFundamentalDomain U₀ D ν)
    (hconj : ∀ γ ∈ Γ, ∃ c : U → U, MeasurePreserving c ν ν ∧ ∀ u, ι (c u) = γ⁻¹ * ι u * γ)
    (φ : G → ℝ≥0∞) (hφ : Measurable φ) :
    ∑' γ : Γ, ∫⁻ u in D, φ ((ι u)⁻¹ * γ) ∂ν = ∑' γ : Γ, ∫⁻ u in D, φ (γ * ι u) ∂ν := by
  haveI : (ι.range.subgroupOf Γ).Normal := ⟨by
    rintro ⟨n, hn⟩ ⟨u, hu⟩ g
    obtain ⟨c, -, hc⟩ := hconj (g : G)⁻¹ (Γ.inv_mem g.2)
    have hu' : ι u = n := hu
    exact ⟨c u, by rw [hc, hu']; simp⟩⟩
  have h1 : ∑' γ : Γ, ∫⁻ u in D, φ ((ι u)⁻¹ * γ) ∂ν = ∑' γ : Γ, ∫⁻ u in D, (fun x => φ x⁻¹) (γ * ι u) ∂ν := by
    rw [← (Equiv.inv Γ).tsum_eq]
    simp
  rw [h1, tsum_setLIntegral_eq_cosets ι hι ν Γ U₀ hle hD (fun x => φ x⁻¹),
    tsum_setLIntegral_eq_cosets ι hι ν Γ U₀ hle hD,
    ← (Equiv.inv (Γ ⧸ ι.range.subgroupOf Γ)).tsum_eq]
  refine tsum_congr fun q => tsum_congr fun _ => ?_
  set t : Γ := (Equiv.inv (Γ ⧸ ι.range.subgroupOf Γ) q).out with ht
  have hmem : t * q.out ∈ ι.range.subgroupOf Γ := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, ht]
    simp
  obtain ⟨v, hv⟩ := hmem
  have hv' : ι v = (t : G) * (q.out : Γ) := hv
  obtain ⟨c, hcm, hc⟩ := hconj (t : G)⁻¹ (Γ.inv_mem t.2)
  calc ∫⁻ u, φ ((t : G) * ι u)⁻¹ ∂ν = ∫⁻ u, φ (ι u * (t : G)⁻¹) ∂ν := by
        rw [← lintegral_inv_eq_self (μ := ν) (fun u => φ (ι u * (t : G)⁻¹))]
        simp
    _ = ∫⁻ u, φ ((t : G)⁻¹ * ι (c u)) ∂ν := by
        refine lintegral_congr fun u => ?_
        rw [hc]; congr 1; group
    _ = ∫⁻ u, φ ((t : G)⁻¹ * ι u) ∂ν :=
        hcm.lintegral_comp (f := fun u => φ ((t : G)⁻¹ * ι u)) (hφ.comp (hιm.const_mul _))
    _ = ∫⁻ u, φ ((t : G)⁻¹ * ι (v * u)) ∂ν :=
        (lintegral_mul_left_eq_self (fun u => φ ((t : G)⁻¹ * ι u)) v).symm
    _ = _ := by
        refine lintegral_congr fun u => ?_
        rw [map_mul, hv']; congr 1; group

omit [MeasurableInv G] in

theorem lintegral_mul_tsum_weight (μ : Measure G) [μ.IsMulLeftInvariant] (Γ : Subgroup G) [Countable Γ] {𝓕 : Set G}
    (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) {β : G → ℝ≥0∞} (hβm : Measurable β)
    (hβ : ∀ f : G → ℝ≥0∞, ∫⁻ g in 𝓕, f g ∂μ = ∫⁻ g, β g * f g ∂μ) (ρ : G → ℝ≥0∞) (hρ : Measurable ρ) (w : G) :
    ∫⁻ g, ρ g * ∑' γ : Γ, β (γ * w * g) ∂μ = ∫⁻ g, ρ g ∂μ := by
  haveI : SMulInvariantMeasure Γ G μ := ⟨fun γ s _ => measure_preimage_mul μ (γ : G) s⟩
  simp_rw [← ENNReal.tsum_mul_left]
  rw [lintegral_tsum (f := fun (γ : Γ) g => ρ g * β (γ * w * g))
      fun γ => (hρ.mul (hβm.comp (measurable_const_mul _))).aemeasurable,
    ← lintegral_mul_left_eq_self ρ w⁻¹, h𝓕.lintegral_eq_tsum']
  refine tsum_congr fun γ => ?_
  rw [hβ, ← lintegral_mul_left_eq_self _ ((γ : G) * w)⁻¹]
  refine lintegral_congr fun g => ?_
  rw [mul_comm, mul_inv_cancel_left]
  congr 2
  change _ = w⁻¹ * (((γ⁻¹ : Γ) : G) * g)
  simp [mul_assoc]

theorem setLIntegral_average (ι : U →* G) (hι : Function.Injective ι) (hιm : Measurable ι)
    (μ : Measure G) [SFinite μ] [μ.IsMulLeftInvariant] (ν : Measure U) [SigmaFinite ν] [ν.IsMulLeftInvariant]
    (Γ : Subgroup G) [Countable Γ] (U₀ : Subgroup U) (hle : ∀ b ∈ U₀, ι b ∈ Γ) (Γ₁ : Set G)
    (hcov : ∀ γ ∈ Γ, ∃ a ∈ Γ₁, ∃ b ∈ U₀, γ = a * ι b)
    (hconj : ∀ a ∈ Γ₁, ∃ c : U → U, MeasurePreserving c ν ν ∧ ∀ u, ι (c u) = a⁻¹ * ι u * a)
    {D : Set U} (hD : IsFundamentalDomain U₀ D ν) (hνD : ν D = 1)
    {𝓕 : Set G} (h𝓕 : IsFundamentalDomain Γ 𝓕 μ)
    (F : G → ℝ≥0∞) (hF : Measurable F) (hinv : ∀ γ ∈ Γ, ∀ g, F (γ * g) = F g) :
    ∫⁻ g in 𝓕, F g ∂μ = ∫⁻ g in 𝓕, ∫⁻ u in D, F (ι u * g) ∂ν ∂μ := by
  haveI : Countable U₀ := (show Function.Injective (fun b : U₀ => (⟨ι b, hle b b.2⟩ : Γ)) from
    fun b b' h => Subtype.ext (hι (congrArg Subtype.val h))).countable
  haveI := isMulRightInvariant_of_covolume_one ν U₀ hD hνD
  haveI := isInvInvariant_of_covolume_one ν U₀ hD hνD
  haveI : SMulInvariantMeasure Γ G μ := ⟨fun γ s _ => measure_preimage_mul μ (γ : G) s⟩
  have hconj' : ∀ γ ∈ Γ, ∃ c : U → U, MeasurePreserving c ν ν ∧ ∀ u, ι (c u) = γ⁻¹ * ι u * γ := by
    intro γ hγ
    obtain ⟨a, ha, b, -, rfl⟩ := hcov γ hγ
    obtain ⟨c, hcm, hc⟩ := hconj a ha
    refine ⟨fun u => b⁻¹ * c u * b,
      (measurePreserving_mul_right ν b).comp ((measurePreserving_mul_left ν b⁻¹).comp hcm), fun u => ?_⟩
    simp only [map_mul, map_inv, hc]; group
  obtain ⟨β, hβm, hβ⟩ : ∃ β : G → ℝ≥0∞, Measurable β ∧
      ∀ f : G → ℝ≥0∞, ∫⁻ g in 𝓕, f g ∂μ = ∫⁻ g, β g * f g ∂μ := by
    refine ⟨(toMeasurable μ 𝓕).indicator 1, measurable_one.indicator (measurableSet_toMeasurable μ 𝓕), fun f => ?_⟩
    rw [← restrict_congr_set h𝓕.nullMeasurableSet.toMeasurable_ae_eq,
      ← lintegral_indicator (measurableSet_toMeasurable μ 𝓕)]
    refine lintegral_congr fun g => ?_
    by_cases hg : g ∈ toMeasurable μ 𝓕 <;> simp [hg]
  have hA : ∀ w : G, ∫⁻ g in 𝓕, F (w * g) ∂μ = ∫⁻ g in 𝓕, F g * ∑' γ : Γ, β (w⁻¹ * γ * g) ∂μ := by
    intro w
    simp_rw [← ENNReal.tsum_mul_left]
    rw [lintegral_tsum (f := fun (γ : Γ) g => F g * β (w⁻¹ * γ * g))
      fun γ => (hF.mul (hβm.comp (measurable_const_mul _))).aemeasurable, hβ,
      ← lintegral_mul_left_eq_self _ w⁻¹, h𝓕.lintegral_eq_tsum'']
    refine tsum_congr fun γ => lintegral_congr fun g => ?_
    change β (w⁻¹ * (γ * g)) * F (w * (w⁻¹ * (γ * g))) = _
    rw [mul_inv_cancel_left, hinv _ γ.2, mul_comm, mul_assoc]
  have hm1 : Measurable fun p : G × U => ∑' γ : Γ, β ((ι p.2)⁻¹ * γ * p.1) :=
    Measurable.ennreal_tsum fun γ => hβm.comp (((hιm.comp measurable_snd).inv.mul_const _).mul measurable_fst)
  have hm2 : Measurable fun p : G × U => ∑' γ : Γ, β (γ * ι p.2 * p.1) :=
    Measurable.ennreal_tsum fun γ => hβm.comp (((hιm.comp measurable_snd).const_mul _).mul measurable_fst)
  symm
  calc ∫⁻ g in 𝓕, ∫⁻ u in D, F (ι u * g) ∂ν ∂μ = ∫⁻ u in D, ∫⁻ g in 𝓕, F (ι u * g) ∂μ ∂ν :=
        lintegral_lintegral_swap (hF.comp ((hιm.comp measurable_snd).mul measurable_fst)).aemeasurable
    _ = ∫⁻ u in D, ∫⁻ g in 𝓕, F g * ∑' γ : Γ, β ((ι u)⁻¹ * γ * g) ∂μ ∂ν := lintegral_congr fun u => hA _
    _ = ∫⁻ g in 𝓕, ∫⁻ u in D, F g * ∑' γ : Γ, β ((ι u)⁻¹ * γ * g) ∂ν ∂μ :=
        (lintegral_lintegral_swap ((hF.comp measurable_fst).mul hm1).aemeasurable).symm
    _ = ∫⁻ g in 𝓕, ∫⁻ u in D, F g * ∑' γ : Γ, β (γ * ι u * g) ∂ν ∂μ := by
        refine lintegral_congr fun g => ?_
        rw [lintegral_const_mul (F g) (f := fun u => ∑' γ : Γ, β ((ι u)⁻¹ * γ * g))
            (hm1.comp measurable_prodMk_left),
          lintegral_const_mul (F g) (f := fun u => ∑' γ : Γ, β (γ * ι u * g)) (hm2.comp measurable_prodMk_left),
          lintegral_tsum (f := fun (γ : Γ) u => β ((ι u)⁻¹ * γ * g))
            fun γ => (hβm.comp ((hιm.inv.mul_const _).mul_const _)).aemeasurable,
          lintegral_tsum (f := fun (γ : Γ) u => β (γ * ι u * g))
            fun γ => (hβm.comp ((hιm.const_mul _).mul_const _)).aemeasurable,
          tsum_setLIntegral_inv ι hι hιm ν Γ U₀ hle hD hconj' (fun x => β (x * g))
            (hβm.comp (measurable_mul_const g))]
    _ = ∫⁻ u in D, ∫⁻ g in 𝓕, F g * ∑' γ : Γ, β (γ * ι u * g) ∂μ ∂ν :=
        lintegral_lintegral_swap ((hF.comp measurable_fst).mul hm2).aemeasurable
    _ = ∫⁻ _u in D, ∫⁻ g in 𝓕, F g ∂μ ∂ν := by
        refine lintegral_congr fun u => ?_
        rw [hβ, hβ F, ← lintegral_mul_tsum_weight μ Γ h𝓕 hβm hβ (fun g => β g * F g) (hβm.mul hF) (ι u)]
        simp_rw [mul_assoc]
    _ = ∫⁻ g in 𝓕, F g ∂μ := by simp [hνD]

end Average

section Additive

variable {G A : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
  [AddGroup A] [MeasurableSpace A] [MeasurableAdd₂ A] [MeasurableNeg A]

end Additive

end GlobalTheory.UnipAvg
