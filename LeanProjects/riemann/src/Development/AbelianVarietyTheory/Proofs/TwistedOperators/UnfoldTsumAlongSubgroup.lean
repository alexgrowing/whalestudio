import Mathlib
open MeasureTheory

namespace GlobalTheory

theorem unfold_tsum_along_subgroup : ∀ (G H : Type) [Group G] [Group H] [MeasurableSpace H] [MeasurableMul H] (ν : Measure H) [ν.IsMulLeftInvariant] (ι : H →* G), Function.Injective ι → ∀ (Γ : Subgroup G) [Countable Γ] (𝓕 : Set H), IsFundamentalDomain (Γ.comap ι) 𝓕 ν → ∀ (f : G → ℂ) (φ : H → ℂ), (∀ γ : G, Measurable fun h => f (γ * ι h)) → Measurable φ → (∀ γ ∈ Γ.comap ι, ∀ h, φ (γ * h) = φ h) → (∑' q : Γ ⧸ ι.range.subgroupOf Γ, ∫⁻ h, ‖f ((q.out : Γ) * ι h) * φ h‖ₑ ∂ν) ≠ ⊤ → IntegrableOn (fun h => (∑' γ : Γ, f (γ * ι h)) * φ h) 𝓕 ν ∧ HasSum (fun q : Γ ⧸ ι.range.subgroupOf Γ => ∫ h, f ((q.out : Γ) * ι h) * φ h ∂ν) (∫ h in 𝓕, (∑' γ : Γ, f (γ * ι h)) * φ h ∂ν) := by
  intro G H _ _ _ _ ν _ ι hι Γ _ 𝓕 h𝓕 f φ hf hφ hφinv hT
  haveI : MeasurableConstSMul (Γ.comap ι) H := ⟨fun g => measurable_const_mul (g : H)⟩
  haveI : SMulInvariantMeasure (Γ.comap ι) H ν := ⟨fun g s _ => measure_preimage_mul ν (g : H) s⟩
  haveI : Countable (Γ.comap ι) := by
    refine Function.Injective.countable (f := fun δ : Γ.comap ι => (⟨ι δ, δ.2⟩ : Γ)) ?_
    intro a b hab
    exact Subtype.ext (hι (congrArg Subtype.val hab))
  let e : (Γ ⧸ ι.range.subgroupOf Γ) × Γ.comap ι → Γ := fun p => (p.1.out : Γ) * ⟨ι p.2, p.2.2⟩
  have hmemK : ∀ δ : Γ.comap ι, (⟨ι δ, δ.2⟩ : Γ) ∈ ι.range.subgroupOf Γ := fun δ => by
    rw [Subgroup.mem_subgroupOf]; exact ⟨δ, rfl⟩
  have he_inj : Function.Injective e := by
    rintro ⟨q, δ⟩ ⟨q', δ'⟩ h
    have hq : ∀ q δ, (QuotientGroup.mk (e (q, δ)) : Γ ⧸ ι.range.subgroupOf Γ) = q := by
      intro q δ
      show (QuotientGroup.mk ((q.out : Γ) * ⟨ι δ, δ.2⟩) : Γ ⧸ ι.range.subgroupOf Γ) = q
      rw [QuotientGroup.mk_mul_of_mem _ (hmemK δ)]
      exact QuotientGroup.out_eq' q
    have hqq : q = q' := by rw [← hq q δ, ← hq q' δ', h]
    subst hqq
    have h2 := mul_left_cancel h
    have h3 : ι δ = ι δ' := congrArg Subtype.val h2
    rw [Prod.mk.injEq]
    exact ⟨rfl, Subtype.ext (hι h3)⟩
  have he_surj : Function.Surjective e := by
    intro γ
    set q : Γ ⧸ ι.range.subgroupOf Γ := QuotientGroup.mk γ with hqdef
    have hm : (q.out : Γ)⁻¹ * γ ∈ ι.range.subgroupOf Γ := by
      apply QuotientGroup.eq.1
      rw [QuotientGroup.out_eq']
    rw [Subgroup.mem_subgroupOf] at hm
    obtain ⟨y, hy⟩ := hm
    have hyΓ : ι y ∈ Γ := by rw [hy]; exact ((q.out : Γ)⁻¹ * γ).2
    refine ⟨(q, ⟨y, hyΓ⟩), ?_⟩
    apply Subtype.ext
    show ((q.out : Γ) : G) * ι y = γ
    rw [hy]
    simp
  let eq := Equiv.ofBijective e ⟨he_inj, he_surj⟩
  let F : Γ → H → ℂ := fun γ h => f ((γ : G) * ι h) * φ h
  let g : Γ ⧸ ι.range.subgroupOf Γ → H → ℂ := fun q h => f (((q.out : Γ) : G) * ι h) * φ h
  have hkey : ∀ q (δ : Γ.comap ι) h, F (e (q, δ)) h = g q (δ • h) := by
    intro q δ h
    show f ((((q.out : Γ) : G) * ι δ) * ι h) * φ h = f (((q.out : Γ) : G) * ι ((δ : H) * h)) * φ ((δ : H) * h)
    rw [map_mul, mul_assoc, hφinv δ δ.2 h]
  have hFm : ∀ γ, Measurable (F γ) := fun γ => (hf γ).mul hφ
  have hgm : ∀ q, Measurable (g q) := fun q => (hf _).mul hφ
  have hA : ∀ q, ∫⁻ h, ‖g q h‖ₑ ∂ν = ∑' δ : Γ.comap ι, ∫⁻ h in 𝓕, ‖F (e (q, δ)) h‖ₑ ∂ν := by
    intro q
    rw [h𝓕.lintegral_eq_tsum'' (fun h => ‖g q h‖ₑ)]
    simp_rw [hkey]
  have hsumF : ∑' γ : Γ, ∫⁻ h in 𝓕, ‖F γ h‖ₑ ∂ν = ∑' q, ∫⁻ h, ‖g q h‖ₑ ∂ν := by
    rw [← eq.tsum_eq]
    calc ∑' p, ∫⁻ h in 𝓕, ‖F (eq p) h‖ₑ ∂ν
        = ∑' q, ∑' δ : Γ.comap ι, ∫⁻ h in 𝓕, ‖F (e (q, δ)) h‖ₑ ∂ν :=
          ENNReal.tsum_prod (f := fun q δ => ∫⁻ h in 𝓕, ‖F (e (q, δ)) h‖ₑ ∂ν)
      _ = _ := by simp_rw [hA]
  have hT' : ∑' γ : Γ, ∫⁻ h in 𝓕, ‖F γ h‖ₑ ∂ν ≠ ⊤ := by rw [hsumF]; exact hT
  have hfun : (fun h => (∑' γ : Γ, f (γ * ι h)) * φ h) = fun h => ∑' γ : Γ, F γ h :=
    funext fun h => tsum_mul_right.symm
  have hint : IntegrableOn (fun h => ∑' γ : Γ, F γ h) 𝓕 ν := by
    refine ⟨(AEMeasurable.tsum fun γ => (hFm γ).aemeasurable).aestronglyMeasurable, ?_⟩
    show ∫⁻ h in 𝓕, ‖∑' γ : Γ, F γ h‖ₑ ∂ν < ⊤
    calc ∫⁻ h in 𝓕, ‖∑' γ : Γ, F γ h‖ₑ ∂ν ≤ ∫⁻ h in 𝓕, ∑' γ, ‖F γ h‖ₑ ∂ν :=
          lintegral_mono fun h => enorm_tsum_le_tsum_enorm
      _ = ∑' γ, ∫⁻ h in 𝓕, ‖F γ h‖ₑ ∂ν := lintegral_tsum fun γ => (hFm γ).aemeasurable.enorm
      _ < ⊤ := lt_top_iff_ne_top.2 hT'
  have hsumm : Summable fun γ : Γ => ∫ h in 𝓕, F γ h ∂ν := by
    refine Summable.of_norm ?_
    have h1 : ∑' γ : Γ, ‖∫ h in 𝓕, F γ h ∂ν‖ₑ ≠ ⊤ :=
      ne_top_of_le_ne_top hT' (ENNReal.tsum_le_tsum fun γ => enorm_integral_le_lintegral_enorm _)
    simp only [enorm_eq_nnnorm] at h1
    exact NNReal.summable_coe.2 (ENNReal.tsum_coe_ne_top_iff_summable.1 h1)
  have hI : ∫ h in 𝓕, (∑' γ : Γ, F γ h) ∂ν = ∑' γ : Γ, ∫ h in 𝓕, F γ h ∂ν :=
    integral_tsum (fun γ => (hFm γ).aestronglyMeasurable) hT'
  have hgint : ∀ q, Integrable (g q) ν := fun q =>
    ⟨(hgm q).aestronglyMeasurable,
      lt_of_le_of_lt (ENNReal.le_tsum (f := fun q => ∫⁻ h, ‖g q h‖ₑ ∂ν) q) (lt_top_iff_ne_top.2 hT)⟩
  have hs : Summable (fun p : (Γ ⧸ ι.range.subgroupOf Γ) × Γ.comap ι => ∫ h in 𝓕, F (eq p) h ∂ν) :=
    (eq.summable_iff).2 hsumm
  have hinner : ∀ q, HasSum (fun δ : Γ.comap ι => ∫ h in 𝓕, F (e (q, δ)) h ∂ν) (∫ h, g q h ∂ν) := by
    intro q
    have h1 := (hs.prod_factor q).hasSum
    rw [h𝓕.integral_eq_tsum'' (g q) (hgint q)]
    simp_rw [← hkey]
    exact h1
  have htot : HasSum (fun p : (Γ ⧸ ι.range.subgroupOf Γ) × Γ.comap ι => ∫ h in 𝓕, F (eq p) h ∂ν)
      (∫ h in 𝓕, (∑' γ : Γ, F γ h) ∂ν) := by
    rw [hI]; exact (eq.hasSum_iff).2 hsumm.hasSum
  rw [hfun]
  exact ⟨hint, htot.prod_fiberwise hinner⟩

end GlobalTheory
