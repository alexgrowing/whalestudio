import Mathlib
open MeasureTheory

namespace GlobalTheory

theorem unfolding_cover_bound (G H : Type) [Group G] [Group H] [MeasurableSpace H] [MeasurableMul H]
    (μ : Measure H) [μ.IsMulLeftInvariant] (ι : H →* G) (hι : Function.Injective ι)
    (Γ : Subgroup G) [Countable Γ] (Kc : Set H)
    (hK : ∀ h, ∃ δ ∈ Γ.comap ι, δ * h ∈ Kc) (F : G → ENNReal)
    (hF : ∀ γ : G, Measurable fun h => F (γ * ι h)) :
    ∑' q : Γ ⧸ ι.range.subgroupOf Γ, ∫⁻ h, F ((q.out : Γ) * ι h) ∂μ
      ≤ ∫⁻ h in Kc, ∑' γ : Γ, F (γ * ι h) ∂μ := by
  classical
  haveI hcH : Countable (Γ.comap ι) := by
    have : Function.Injective (fun δ : Γ.comap ι => (⟨ι δ, δ.2⟩ : Γ)) := by
      intro a b hab
      apply Subtype.ext
      apply hι
      simpa using congrArg Subtype.val hab
    exact this.countable
  have step : ∀ g : G, ∫⁻ h, F (g * ι h) ∂μ
      ≤ ∑' δ : Γ.comap ι, ∫⁻ k in Kc, F (g * ι ((δ:H)⁻¹) * ι k) ∂μ := by
    intro g
    have hcov : (Set.univ : Set H) = ⋃ δ : Γ.comap ι, (fun h => (δ:H) * h) ⁻¹' Kc := by
      ext h
      simp only [Set.mem_univ, Set.mem_iUnion, Set.mem_preimage, true_iff]
      obtain ⟨δ, hδ, hδK⟩ := hK h
      exact ⟨⟨δ, hδ⟩, hδK⟩
    calc ∫⁻ h, F (g * ι h) ∂μ
        = ∫⁻ h in ⋃ δ : Γ.comap ι, (fun h => (δ:H) * h) ⁻¹' Kc, F (g * ι h) ∂μ := by
          rw [← hcov, Measure.restrict_univ]
      _ ≤ ∑' δ : Γ.comap ι, ∫⁻ h in (fun h => (δ:H) * h) ⁻¹' Kc, F (g * ι h) ∂μ :=
          lintegral_iUnion_le _ _
      _ = ∑' δ : Γ.comap ι, ∫⁻ k in Kc, F (g * ι ((δ:H)⁻¹) * ι k) ∂μ := by
          congr 1; funext δ
          set e := MeasurableEquiv.mulLeft ((δ:H)⁻¹) with he
          have hmap : μ.map e = μ := by
            rw [MeasurableEquiv.coe_mulLeft]; exact map_mul_left_eq_self μ _
          have hpre : e ⁻¹' ((fun h => (δ:H) * h) ⁻¹' Kc) = Kc := by
            ext k; simp [e]
          calc ∫⁻ h in (fun h => (δ:H) * h) ⁻¹' Kc, F (g * ι h) ∂μ
              = ∫⁻ h in (fun h => (δ:H) * h) ⁻¹' Kc, F (g * ι h) ∂(μ.map e) := by rw [hmap]
            _ = ∫⁻ h, F (g * ι h) ∂((μ.restrict (e ⁻¹' ((fun h => (δ:H) * h) ⁻¹' Kc))).map e) := by
                rw [e.restrict_map]
            _ = ∫⁻ k, F (g * ι (e k)) ∂(μ.restrict (e ⁻¹' ((fun h => (δ:H) * h) ⁻¹' Kc))) :=
                lintegral_map_equiv _ _
            _ = _ := by rw [hpre]; simp [e, mul_assoc]
  haveI : Countable (Γ ⧸ ι.range.subgroupOf Γ) := QuotientGroup.mk_surjective.countable
  let φ : (Γ ⧸ ι.range.subgroupOf Γ) × Γ.comap ι → Γ := fun p =>
    (p.1.out : Γ) * ⟨ι ((p.2 : H)⁻¹), by simpa using Γ.inv_mem p.2.2⟩
  have hφ : Function.Injective φ := by
    rintro ⟨q₁, δ₁⟩ ⟨q₂, δ₂⟩ h
    have hv := congrArg Subtype.val h
    simp only [φ, Subgroup.coe_mul] at hv
    have hq : q₁ = q₂ := by
      rw [← QuotientGroup.out_eq' q₁, ← QuotientGroup.out_eq' q₂, QuotientGroup.eq,
        Subgroup.mem_subgroupOf, MonoidHom.mem_range]
      refine ⟨(δ₁:H)⁻¹ * (δ₂:H), ?_⟩
      rw [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [show ((q₁.out : Γ) : G)⁻¹ * ((q₂.out : Γ) : G)
          = ((q₁.out : Γ) : G)⁻¹ * (((q₂.out : Γ) : G) * ι ((δ₂:H)⁻¹)) * ι (δ₂:H) by
            rw [map_inv]; group, ← hv]
      simp only [map_mul, map_inv]; group
    subst hq
    have h2 : ι ((δ₁:H)⁻¹) = ι ((δ₂:H)⁻¹) := mul_left_cancel hv
    have h3 : (δ₁:H)⁻¹ = (δ₂:H)⁻¹ := hι h2
    simp only [Prod.mk.injEq, true_and]
    exact Subtype.ext (inv_injective h3)
  calc ∑' q : Γ ⧸ ι.range.subgroupOf Γ, ∫⁻ h, F ((q.out : Γ) * ι h) ∂μ
      ≤ ∑' q : Γ ⧸ ι.range.subgroupOf Γ, ∑' δ : Γ.comap ι,
          ∫⁻ k in Kc, F (((φ (q, δ)) : G) * ι k) ∂μ := by
        refine ENNReal.tsum_le_tsum fun q => ?_
        exact step _
    _ = ∑' p, ∫⁻ k in Kc, F ((φ p : G) * ι k) ∂μ := ENNReal.tsum_prod.symm
    _ = ∫⁻ k in Kc, ∑' p, F ((φ p : G) * ι k) ∂μ :=
        (lintegral_tsum fun p => (hF _).aemeasurable).symm
    _ ≤ ∫⁻ h in Kc, ∑' γ : Γ, F (γ * ι h) ∂μ :=
        lintegral_mono fun k => ENNReal.tsum_comp_le_tsum_of_injective hφ (fun γ : Γ => F (γ * ι k))

end GlobalTheory
