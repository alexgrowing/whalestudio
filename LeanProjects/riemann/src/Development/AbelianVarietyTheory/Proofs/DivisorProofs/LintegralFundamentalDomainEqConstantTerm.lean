import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FundamentalDomainIndicatorTsumOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FundamentalDomainSubgroupMeasureConst
open MeasureTheory
open scoped Pointwise

namespace GlobalTheory.CtAbs

theorem tsum_eq_tsum_quotient {H : Type} [Group H] (K : Subgroup H) (f : H → ENNReal) :
    ∑' h : H, f h = ∑' q : H ⧸ K, ∑' k : K, f (q.out * k) := by
  classical
  have hbij : Function.Bijective (fun p : (H ⧸ K) × K => p.1.out * (p.2 : H)) := by
    constructor
    · rintro ⟨q, k⟩ ⟨q', k'⟩ h
      simp only at h
      have h1 : ((q.out * (k : H) : H) : H ⧸ K) = q := by
        rw [QuotientGroup.mk_mul_of_mem _ k.2, QuotientGroup.out_eq']
      have h2 : ((q'.out * (k' : H) : H) : H ⧸ K) = q' := by
        rw [QuotientGroup.mk_mul_of_mem _ k'.2, QuotientGroup.out_eq']
      have hq : q = q' := by rw [← h1, ← h2, h]
      subst hq
      have : (k : H) = k' := mul_left_cancel h
      exact Prod.ext rfl (Subtype.ext this)
    · intro h
      refine ⟨((h : H ⧸ K), ⟨((h : H ⧸ K).out)⁻¹ * h,
        QuotientGroup.eq.1 (QuotientGroup.out_eq' (h : H ⧸ K))⟩), ?_⟩
      simp
  rw [← (Equiv.ofBijective _ hbij).tsum_eq f]
  exact ENNReal.tsum_prod (f := fun (q : H ⧸ K) (k : K) => f (q.out * k))

end GlobalTheory.CtAbs

namespace GlobalTheory.CtAbs

theorem countable_subgroupOf {G : Type} [Group G] (N Γ : Subgroup G) [Countable Γ] :
    Countable (Γ.subgroupOf N) := by
  refine Function.Injective.countable
    (f := fun x : Γ.subgroupOf N => (⟨((x : N) : G), Subgroup.mem_subgroupOf.1 x.2⟩ : Γ)) ?_
  intro a b h
  have h' : ((a : N) : G) = ((b : N) : G) := by simpa using congrArg Subtype.val h
  exact Subtype.ext (Subtype.ext h')

theorem tsum_setLIntegral_inv_mul {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul₂ G]
    [MeasurableInv G] (N Γ : Subgroup G) [Countable Γ] (ν : Measure N) [ν.IsMulLeftInvariant]
    (hinv : MeasurePreserving (fun u : N => u⁻¹) ν ν)
    (hnorm : ∀ γ ∈ Γ, ∀ u ∈ N, γ * u * γ⁻¹ ∈ N)
    (hconj : ∀ γ ∈ Γ, ∀ f : G → ENNReal, Measurable f →
      ∫⁻ u, f (u.1 * γ) ∂ν = ∫⁻ u, f (γ * u.1) ∂ν)
    (𝓕 : Set N) (h𝓕 : IsFundamentalDomain (Γ.subgroupOf N) 𝓕 ν)
    (β : G → ENNReal) (hβ : Measurable β) (g : G) :
    ∑' γ : Γ, ∫⁻ u in 𝓕, β ((u : G)⁻¹ * ((γ : G) * g)) ∂ν
      = ∫⁻ u in 𝓕, ∑' γ : Γ, β ((γ : G) * u * g) ∂ν := by
  classical
  haveI := countable_subgroupOf N Γ
  have hmulN : ∀ a : N, Measurable (fun x : N => a * x) := fun a =>
    ((measurable_const_mul (a : G)).comp measurable_subtype_coe).subtype_mk
  haveI : MeasurableConstSMul (Γ.subgroupOf N) N := ⟨fun c => hmulN (c : N)⟩
  haveI : SMulInvariantMeasure (Γ.subgroupOf N) N ν := ⟨fun c s hs => by
    show ν ((fun x : N => (c : N) * x) ⁻¹' s) = ν s
    rw [← Measure.map_apply (hmulN _) hs, map_mul_left_eq_self]⟩
  set K : Subgroup Γ := N.subgroupOf Γ with hK

  let eKN : K ≃ Γ.subgroupOf N :=
    { toFun := fun k => ⟨⟨((k : Γ) : G), Subgroup.mem_subgroupOf.1 k.2⟩,
        Subgroup.mem_subgroupOf.2 (k : Γ).2⟩
      invFun := fun ε => ⟨⟨((ε : N) : G), Subgroup.mem_subgroupOf.1 ε.2⟩,
        Subgroup.mem_subgroupOf.2 (ε : N).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  haveI : Countable (Γ ⧸ K) := (QuotientGroup.mk_surjective (s := K)).countable
  have hcoset : ∀ s : Γ, ∑' k : K, ∫⁻ u in 𝓕, β ((u : G)⁻¹ * (((s * (k : Γ) : Γ) : G) * g)) ∂ν
      = ∫⁻ u in 𝓕, ∑' k : K, β ((s : G) * ((k : Γ) : G) * u * g) ∂ν := by
    intro s
    have hmemN : ∀ k : K, (s : G) * ((k : Γ) : G)⁻¹ * (s : G)⁻¹ ∈ N := fun k =>
      hnorm _ s.2 _ (N.inv_mem (Subgroup.mem_subgroupOf.1 k.2))
    have hmemΓ : ∀ k : K, (s : G) * ((k : Γ) : G)⁻¹ * (s : G)⁻¹ ∈ Γ := fun k =>
      Γ.mul_mem (Γ.mul_mem s.2 (Γ.inv_mem (k : Γ).2)) (Γ.inv_mem s.2)
    have hmemN' : ∀ ε : Γ.subgroupOf N, (s : G)⁻¹ * ((ε : N) : G)⁻¹ * (s : G) ∈ N := by
      intro ε
      have := hnorm _ (Γ.inv_mem s.2) _ (N.inv_mem (ε : N).2)
      rwa [inv_inv] at this
    have hmemΓ' : ∀ ε : Γ.subgroupOf N, (s : G)⁻¹ * ((ε : N) : G)⁻¹ * (s : G) ∈ Γ := fun ε =>
      Γ.mul_mem (Γ.mul_mem (Γ.inv_mem s.2) (Γ.inv_mem (Subgroup.mem_subgroupOf.1 ε.2))) s.2
    let e : K ≃ Γ.subgroupOf N :=
      { toFun := fun k => ⟨⟨(s : G) * ((k : Γ) : G)⁻¹ * (s : G)⁻¹, hmemN k⟩, hmemΓ k⟩
        invFun := fun ε => ⟨⟨(s : G)⁻¹ * ((ε : N) : G)⁻¹ * (s : G), hmemΓ' ε⟩,
          Subgroup.mem_subgroupOf.2 (hmemN' ε)⟩
        left_inv := fun k => Subtype.ext <| Subtype.ext <| by dsimp; group
        right_inv := fun ε => Subtype.ext <| Subtype.ext <| by dsimp; group }
    have hh : Measurable (fun v : N => β ((v : G)⁻¹ * ((s : G) * g))) :=
      hβ.comp (measurable_subtype_coe.inv.mul_const _)
    have hf2 : Measurable (fun x : G => β (x * g)) := hβ.comp (measurable_mul_const g)
    calc ∑' k : K, ∫⁻ u in 𝓕, β ((u : G)⁻¹ * (((s * (k : Γ) : Γ) : G) * g)) ∂ν
        = ∑' k : K, ∫⁻ u in 𝓕, β ((((e k • u : N)) : G)⁻¹ * ((s : G) * g)) ∂ν := by
          refine tsum_congr fun k => lintegral_congr fun u => ?_
          congr 1
          simp only [e, Equiv.coe_fn_mk, Subgroup.smul_def, smul_eq_mul, Subgroup.coe_mul]
          group
      _ = ∑' ε : Γ.subgroupOf N, ∫⁻ u in 𝓕, β ((((ε • u : N)) : G)⁻¹ * ((s : G) * g)) ∂ν :=
          e.tsum_eq (fun ε => ∫⁻ u in 𝓕, β ((((ε • u : N)) : G)⁻¹ * ((s : G) * g)) ∂ν)
      _ = ∫⁻ v, β ((v : G)⁻¹ * ((s : G) * g)) ∂ν := (h𝓕.lintegral_eq_tsum'' (fun v : N => β ((v : G)⁻¹ * ((s : G) * g)))).symm
      _ = ∫⁻ v, β ((v : G) * (s : G) * g) ∂ν := by
          have hm3 : Measurable (fun v : N => β ((v : G) * (s : G) * g)) :=
            hβ.comp ((measurable_subtype_coe.mul_const _).mul_const _)
          rw [← hinv.lintegral_comp hm3]
          refine lintegral_congr fun v => ?_
          simp only [Subgroup.coe_inv, mul_assoc]
      _ = ∫⁻ v, β ((s : G) * (v : G) * g) ∂ν := hconj s s.2 _ hf2
      _ = ∑' ε : Γ.subgroupOf N, ∫⁻ u in 𝓕, β ((s : G) * ((ε • u : N) : G) * g) ∂ν :=
          h𝓕.lintegral_eq_tsum'' (fun v : N => β ((s : G) * (v : G) * g))
      _ = ∫⁻ u in 𝓕, ∑' ε : Γ.subgroupOf N, β ((s : G) * ((ε • u : N) : G) * g) ∂ν := by
          rw [lintegral_tsum]
          intro ε
          exact (hβ.comp (((measurable_const_mul _).comp
            (measurable_subtype_coe.comp (hmulN (ε : N)))).mul_const _)).aemeasurable
      _ = ∫⁻ u in 𝓕, ∑' k : K, β ((s : G) * ((k : Γ) : G) * u * g) ∂ν := by
          refine lintegral_congr fun u => ?_
          rw [← eKN.tsum_eq]
          refine tsum_congr fun k => ?_
          simp only [eKN, Equiv.coe_fn_mk, Subgroup.smul_def, smul_eq_mul, Subgroup.coe_mul, mul_assoc]
  calc ∑' γ : Γ, ∫⁻ u in 𝓕, β ((u : G)⁻¹ * ((γ : G) * g)) ∂ν
      = ∑' q : Γ ⧸ K, ∑' k : K, ∫⁻ u in 𝓕, β ((u : G)⁻¹ * (((q.out * (k : Γ) : Γ) : G) * g)) ∂ν :=
        tsum_eq_tsum_quotient K (fun γ : Γ => ∫⁻ u in 𝓕, β ((u : G)⁻¹ * ((γ : G) * g)) ∂ν)
    _ = ∑' q : Γ ⧸ K, ∫⁻ u in 𝓕, ∑' k : K, β (((q.out : Γ) : G) * ((k : Γ) : G) * u * g) ∂ν :=
        tsum_congr fun q => hcoset q.out
    _ = ∫⁻ u in 𝓕, ∑' q : Γ ⧸ K, ∑' k : K, β (((q.out : Γ) : G) * ((k : Γ) : G) * u * g) ∂ν := by
        rw [lintegral_tsum]
        intro q
        refine (Measurable.ennreal_tsum fun k => ?_).aemeasurable
        exact hβ.comp ((measurable_subtype_coe.const_mul _).mul_const _)
    _ = ∫⁻ u in 𝓕, ∑' γ : Γ, β ((γ : G) * u * g) ∂ν := by
        refine lintegral_congr fun u => ?_
        rw [tsum_eq_tsum_quotient K (fun γ : Γ => β ((γ : G) * u * g))]
        simp only [Subgroup.coe_mul]

end GlobalTheory.CtAbs

namespace GlobalTheory

open GlobalTheory.CtAbs in

theorem lintegral_fundamentalDomain_eq_constantTerm :
    ∀ {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G] (μ : Measure G) [SFinite μ] [μ.IsMulLeftInvariant]
    (N Γ : Subgroup G) [Countable Γ] (ν : Measure N) [SFinite ν] [ν.IsMulLeftInvariant], MeasurePreserving (fun u : N => u⁻¹) ν ν →
    (∀ γ ∈ Γ, ∀ u ∈ N, γ * u * γ⁻¹ ∈ N) →
    (∀ γ ∈ Γ, ∀ f : G → ENNReal, Measurable f → ∫⁻ u, f (u.1 * γ) ∂ν = ∫⁻ u, f (γ * u.1) ∂ν) →
    ∀ 𝓕 : Set N, IsFundamentalDomain (Γ.subgroupOf N) 𝓕 ν → ν 𝓕 = 1 → ∀ 𝓓 : Set G, IsFundamentalDomain Γ 𝓓 μ →
    ∀ φ : G → ENNReal, Measurable φ → (∀ γ ∈ Γ, ∀ g, φ (γ * g) = φ g) →
      ∫⁻ g in 𝓓, φ g ∂μ = ∫⁻ g in 𝓓, ∫⁻ u in 𝓕, φ (u.1 * g) ∂ν ∂μ := by
  intro G _ _ _ _ μ _ _ N Γ _ ν _ _ hinv hnorm hconj 𝓕 h𝓕 h1 𝓓 h𝓓 φ hφ hφinv
  classical
  obtain ⟨D, hDsub, hDm, hDae⟩ := h𝓓.nullMeasurableSet.exists_measurable_subset_ae_eq
  obtain ⟨F, -, hFm, hFae⟩ := h𝓕.nullMeasurableSet.exists_measurable_subset_ae_eq
  set β : G → ENNReal := D.indicator 1 with hβdef
  have hβ : Measurable β := measurable_one.indicator hDm
  have hFind : ∀ h : N → ENNReal, ∫⁻ u, F.indicator 1 u * h u ∂ν = ∫⁻ u in 𝓕, h u ∂ν := by
    intro h
    rw [Measure.restrict_congr_set hFae.symm, ← lintegral_indicator hFm]
    refine lintegral_congr fun u => ?_
    by_cases hu : u ∈ F <;> simp [hu]
  have hFi : Measurable (F.indicator (1 : N → ENNReal)) := measurable_one.indicator hFm

  have hcount : ∀ᵐ y ∂μ, ∑' γ : Γ, β ((γ : G) * y) = 1 :=
    fundamentalDomain_count_ae_eq_one μ Γ 𝓓 D inferInstance (fun a => measurable_const_mul a)
      inferInstance h𝓓 hDm hDsub (ae_eq_set.1 hDae).2
  have hS : ∀ᵐ g ∂μ, ∑' γ : Γ, ∫⁻ u in 𝓕, β ((u : G)⁻¹ * ((γ : G) * g)) ∂ν = 1 := by
    filter_upwards [ae_ae_subgroup_mul_of_ae μ N ν hcount] with g hg
    rw [tsum_setLIntegral_inv_mul N Γ ν hinv hnorm hconj 𝓕 h𝓕 β hβ g]
    calc ∫⁻ u in 𝓕, ∑' γ : Γ, β ((γ : G) * u * g) ∂ν = ∫⁻ u in 𝓕, 1 ∂ν :=
          lintegral_congr_ae (ae_restrict_of_ae (hg.mono fun u hu => by simpa [mul_assoc] using hu))
      _ = 1 := by rw [setLIntegral_one, h1]
  haveI : MeasurableConstSMul Γ G := ⟨fun c => measurable_const_mul (c : G)⟩
  haveI : SMulInvariantMeasure Γ G μ := ⟨fun c s hs => by
    show μ (((c : G) * ·) ⁻¹' s) = μ s
    rw [← Measure.map_apply (measurable_const_mul _) hs, map_mul_left_eq_self]⟩
  set T : G → ENNReal := fun g => ∫⁻ u, F.indicator 1 u * β ((u : G)⁻¹ * g) ∂ν with hTdef
  have hTm : Measurable T := by
    have : Measurable (fun p : G × N => F.indicator (1 : N → ENNReal) p.2 * β ((p.2 : G)⁻¹ * p.1)) :=
      (hFi.comp measurable_snd).mul
        (hβ.comp ((measurable_subtype_coe.comp measurable_snd).inv.mul measurable_fst))
    exact this.lintegral_prod_right'
  have hJ1 : Measurable (Function.uncurry fun (g : G) (u : N) =>
      β g * (F.indicator 1 u * φ ((u : G) * g))) :=
    (hβ.comp measurable_fst).mul ((hFi.comp measurable_snd).mul
      (hφ.comp ((measurable_subtype_coe.comp measurable_snd).mul measurable_fst)))
  have hJ2 : Measurable (Function.uncurry fun (u : N) (g : G) =>
      β ((u : G)⁻¹ * g) * (F.indicator 1 u * φ g)) :=
    (hβ.comp ((measurable_subtype_coe.comp measurable_fst).inv.mul measurable_snd)).mul
      ((hFi.comp measurable_fst).mul (hφ.comp measurable_snd))
  symm
  calc ∫⁻ g in 𝓓, ∫⁻ u in 𝓕, φ ((u : G) * g) ∂ν ∂μ
      = ∫⁻ g, ∫⁻ u, β g * (F.indicator 1 u * φ ((u : G) * g)) ∂ν ∂μ := by
        rw [Measure.restrict_congr_set hDae.symm, ← lintegral_indicator hDm]
        refine lintegral_congr fun g => ?_
        have hm : Measurable (fun u : N => F.indicator (1 : N → ENNReal) u * φ ((u : G) * g)) :=
          hFi.mul (hφ.comp (measurable_subtype_coe.mul_const g))
        rw [lintegral_const_mul _ hm, hFind]
        by_cases hg : g ∈ D <;> simp [β, hg]
    _ = ∫⁻ u, ∫⁻ g, β g * (F.indicator 1 u * φ ((u : G) * g)) ∂μ ∂ν :=
        lintegral_lintegral_swap hJ1.aemeasurable
    _ = ∫⁻ u, ∫⁻ g, β ((u : G)⁻¹ * g) * (F.indicator 1 u * φ g) ∂μ ∂ν := by
        refine lintegral_congr fun u => ?_
        rw [← lintegral_mul_left_eq_self (fun g => β ((u : G)⁻¹ * g) * (F.indicator 1 u * φ g)) (u : G)]
        simp only [inv_mul_cancel_left]
    _ = ∫⁻ g, ∫⁻ u, β ((u : G)⁻¹ * g) * (F.indicator 1 u * φ g) ∂ν ∂μ :=
        lintegral_lintegral_swap hJ2.aemeasurable
    _ = ∫⁻ g, φ g * T g ∂μ := by
        refine lintegral_congr fun g => ?_
        have hm : Measurable (fun u : N => F.indicator (1 : N → ENNReal) u * β ((u : G)⁻¹ * g)) :=
          hFi.mul (hβ.comp (measurable_subtype_coe.inv.mul_const g))
        rw [hTdef]
        dsimp only
        rw [← lintegral_const_mul _ hm]
        refine lintegral_congr fun u => ?_
        ring
    _ = ∑' γ : Γ, ∫⁻ g in 𝓓, φ (γ • g) * T (γ • g) ∂μ := h𝓓.lintegral_eq_tsum'' _
    _ = ∑' γ : Γ, ∫⁻ g in 𝓓, φ g * T ((γ : G) * g) ∂μ := by
        refine tsum_congr fun γ => lintegral_congr fun g => ?_
        rw [Subgroup.smul_def, smul_eq_mul, hφinv γ γ.2]
    _ = ∫⁻ g in 𝓓, ∑' γ : Γ, φ g * T ((γ : G) * g) ∂μ := by
        rw [lintegral_tsum]
        intro γ
        exact (hφ.mul (hTm.comp (measurable_const_mul _))).aemeasurable
    _ = ∫⁻ g in 𝓓, φ g * ∑' γ : Γ, ∫⁻ u in 𝓕, β ((u : G)⁻¹ * ((γ : G) * g)) ∂ν ∂μ := by
        refine lintegral_congr fun g => ?_
        rw [ENNReal.tsum_mul_left]
        simp only [hTdef, hFind]
    _ = ∫⁻ g in 𝓓, φ g ∂μ := by
        refine lintegral_congr_ae (ae_restrict_of_ae (hS.mono fun g hg => ?_))
        dsimp only
        rw [hg, mul_one]

end GlobalTheory
