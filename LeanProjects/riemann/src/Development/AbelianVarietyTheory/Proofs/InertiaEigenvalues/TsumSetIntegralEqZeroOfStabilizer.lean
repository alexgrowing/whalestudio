import Mathlib
open MeasureTheory MulAction
open scoped Pointwise ENNReal

namespace GlobalTheory

section SlopeTestRemainingChoices
variable {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul G]

theorem setIntegral_subgroup_mul_left (ν : Measure G) [ν.IsMulLeftInvariant] {Λ : Subgroup G}
    (c : Λ) (f : G → ℂ) (s : Set G) :
    ∫ g in s, f ((c : G) * g) ∂ν = ∫ g in c • s, f g ∂ν := by
  have hpre : (fun g : G => (c : G) * g) ⁻¹' (c • s) = s := by
    ext g
    simp [Set.mem_smul_set_iff_inv_smul_mem, Subgroup.smul_def]
  have h := (measurePreserving_mul_left ν (c : G)).setIntegral_preimage_emb
    (measurableEmbedding_mulLeft (c : G)) f (c • s)
  rwa [hpre] at h

theorem setLIntegral_subgroup_mul_left (ν : Measure G) [ν.IsMulLeftInvariant] {Λ : Subgroup G}
    (c : Λ) (f : G → ℝ≥0∞) (s : Set G) :
    ∫⁻ g in s, f ((c : G) * g) ∂ν = ∫⁻ g in c • s, f g ∂ν := by
  have hpre : (fun g : G => (c : G) * g) ⁻¹' (c • s) = s := by
    ext g
    simp [Set.mem_smul_set_iff_inv_smul_mem, Subgroup.smul_def]
  have h := (measurePreserving_mul_left ν (c : G)).setLIntegral_comp_preimage_emb
    (measurableEmbedding_mulLeft (c : G)) f (c • s)
  rwa [hpre] at h

theorem isFundamentalDomain_iUnion_inv_smul {ν : Measure G} [ν.IsMulLeftInvariant]
    {Λ : Subgroup G} [Countable Λ] {𝓖 : Set G} (h : IsFundamentalDomain Λ 𝓖 ν)
    (S : Subgroup Λ) [Countable (Λ ⧸ S)] :
    IsFundamentalDomain (S.map Λ.subtype) (⋃ q : Λ ⧸ S, (q.out)⁻¹ • 𝓖) ν where
  nullMeasurableSet := .iUnion fun q => h.nullMeasurableSet_smul _
  ae_covers := by
    filter_upwards [h.ae_covers] with g hg
    obtain ⟨l, hl⟩ := hg
    have hs : ((QuotientGroup.mk l : Λ ⧸ S).out)⁻¹ * l ∈ S :=
      QuotientGroup.eq.mp (QuotientGroup.out_eq' _)
    refine ⟨⟨(((QuotientGroup.mk l : Λ ⧸ S).out⁻¹ * l : Λ) : G), ⟨_, hs, rfl⟩⟩,
      Set.mem_iUnion.2 ⟨QuotientGroup.mk l, ?_⟩⟩
    rw [Set.mem_inv_smul_set_iff]
    simpa [Subgroup.smul_def, mul_assoc] using hl
  aedisjoint := by
    rintro ⟨s, hs⟩ ⟨t, ht⟩ hst
    obtain ⟨s', hs', rfl⟩ := Subgroup.mem_map.1 hs
    obtain ⟨t', ht', rfl⟩ := Subgroup.mem_map.1 ht
    have hsub : (⟨Λ.subtype s', hs⟩ : S.map Λ.subtype) • (⋃ q : Λ ⧸ S, (q.out)⁻¹ • 𝓖) ∩
        (⟨Λ.subtype t', ht⟩ : S.map Λ.subtype) • (⋃ q : Λ ⧸ S, (q.out)⁻¹ • 𝓖) ⊆
        ⋃ q : Λ ⧸ S, ⋃ r : Λ ⧸ S, ((s' * (q.out)⁻¹) • 𝓖 ∩ (t' * (r.out)⁻¹) • 𝓖) := by
      rintro x ⟨hx1, hx2⟩
      rw [Set.mem_smul_set_iff_inv_smul_mem, Set.mem_iUnion] at hx1 hx2
      obtain ⟨q, hq⟩ := hx1
      obtain ⟨r, hr⟩ := hx2
      rw [Set.mem_inv_smul_set_iff] at hq hr
      refine Set.mem_iUnion.2 ⟨q, Set.mem_iUnion.2 ⟨r, ?_, ?_⟩⟩
      · rw [Set.mem_smul_set_iff_inv_smul_mem]
        simpa [Subgroup.smul_def, mul_assoc] using hq
      · rw [Set.mem_smul_set_iff_inv_smul_mem]
        simpa [Subgroup.smul_def, mul_assoc] using hr
    refine measure_mono_null hsub (measure_iUnion_null fun q => measure_iUnion_null fun r => ?_)
    apply h.aedisjoint
    intro he
    apply hst
    have he' : (q.out) * s'⁻¹ = (r.out) * t'⁻¹ := by
      have := congrArg (·⁻¹) he
      simpa [mul_inv_rev] using this
    have hqr : q = r := by
      rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' r]
      apply QuotientGroup.eq.mpr
      have : (q.out)⁻¹ * r.out = s'⁻¹ * t' := by
        rw [← mul_inv_eq_iff_eq_mul.mpr he'.symm]
        group
      rw [this]
      exact S.mul_mem (S.inv_mem hs') ht'
    subst hqr
    have : s' = t' := by simpa using he'
    subst this
    rfl

end SlopeTestRemainingChoices

theorem tsum_setIntegral_eq_zero_of_stabilizer :
    ∀ {G X : Type} [Group G] [MeasurableSpace G] [MeasurableMul G] (ν : Measure G)
    [ν.IsMulLeftInvariant], SFinite ν → ∀ (Λ : Subgroup G), Countable Λ → ∀ 𝓖 : Set G,
    IsFundamentalDomain Λ 𝓖 ν → ∀ (a : Λ → X → X), (∀ x, a 1 x = x) →
    (∀ γ δ x, a (γ * δ) x = a γ (a δ x)) → ∀ F : X → G → ℂ,
    (∀ γ x g, F (a γ x) g = F x ((γ : G)⁻¹ * g)) → (∀ x, AEStronglyMeasurable (F x) ν) →
    ∑' x, ∫⁻ g in 𝓖, ‖F x g‖ₑ ∂ν ≠ ⊤ →
    (∀ x (Γ : Subgroup G), (∀ g, g ∈ Γ ↔ ∃ h : g ∈ Λ, a ⟨g, h⟩ x = x) → ∀ 𝓓 : Set G,
      IsFundamentalDomain Γ 𝓓 ν → IntegrableOn (F x) 𝓓 ν → ∫ g in 𝓓, F x g ∂ν = 0) →
    ∑' x, ∫ g in 𝓖, F x g ∂ν = 0 := by
  intro G X _ _ _ ν _ _ Λ hΛ 𝓖 h𝓖 a ha1 ham F hF hmeas hfin hzero
  letI : MulAction Λ X := { smul := a, one_smul := ha1, mul_smul := ham }
  have hsmul : ∀ (γ : Λ) (x : X), γ • x = a γ x := fun _ _ => rfl
  set T : X → ℂ := fun x => ∫ g in 𝓖, F x g ∂ν with hTdef
  have hT : ∀ (γ : Λ) x, T (γ • x) = ∫ g in γ⁻¹ • 𝓖, F x g ∂ν := by
    intro γ x
    rw [← setIntegral_subgroup_mul_left ν γ⁻¹]
    simp only [hTdef, hsmul, hF, Subgroup.coe_inv]
  have hL : ∀ (γ : Λ) x, ∫⁻ g in 𝓖, ‖F (γ • x) g‖ₑ ∂ν = ∫⁻ g in γ⁻¹ • 𝓖, ‖F x g‖ₑ ∂ν := by
    intro γ x
    rw [← setLIntegral_subgroup_mul_left ν γ⁻¹]
    simp only [hsmul, hF, Subgroup.coe_inv]
  have hsum : Summable T := by
    refine Summable.of_norm ?_
    have h1 : ∑' x, ‖T x‖ₑ ≠ ⊤ := ne_top_of_le_ne_top hfin
      (ENNReal.tsum_le_tsum fun x => enorm_integral_le_lintegral_enorm _)
    simpa using ENNReal.summable_toReal h1
  have horb : ∀ x₀ : X,
      HasSum (fun q : Λ ⧸ stabilizer Λ x₀ => T (ofQuotientStabilizer Λ x₀ q)) 0 := by
    intro x₀
    set S := stabilizer Λ x₀ with hSdef
    haveI : Countable (Λ ⧸ S) := QuotientGroup.mk_surjective.countable
    have hofq : ∀ q : Λ ⧸ S, ofQuotientStabilizer Λ x₀ q = q.out • x₀ := by
      intro q
      conv_lhs => rw [← QuotientGroup.out_eq' q]
      rfl
    have hinj : Function.Injective fun q : Λ ⧸ S => q.out • x₀ := by
      intro q r hqr
      exact injective_ofQuotientStabilizer Λ x₀ (by simpa only [hofq] using hqr)
    have hD := isFundamentalDomain_iUnion_inv_smul h𝓖 S
    have hdisj : Pairwise (Function.onFun (AEDisjoint ν) fun q : Λ ⧸ S => (q.out)⁻¹ • 𝓖) := by
      intro q r hqr
      refine h𝓖.aedisjoint fun e => hqr ?_
      exact Quotient.out_injective (inv_injective e)
    have hint : IntegrableOn (F x₀) (⋃ q : Λ ⧸ S, (q.out)⁻¹ • 𝓖) ν := by
      refine ⟨(hmeas x₀).restrict, ?_⟩
      show ∫⁻ g in ⋃ q : Λ ⧸ S, (q.out)⁻¹ • 𝓖, ‖F x₀ g‖ₑ ∂ν < ⊤
      calc ∫⁻ g in ⋃ q : Λ ⧸ S, (q.out)⁻¹ • 𝓖, ‖F x₀ g‖ₑ ∂ν
          ≤ ∑' q : Λ ⧸ S, ∫⁻ g in (q.out)⁻¹ • 𝓖, ‖F x₀ g‖ₑ ∂ν := lintegral_iUnion_le _ _
        _ = ∑' q : Λ ⧸ S, ∫⁻ g in 𝓖, ‖F (q.out • x₀) g‖ₑ ∂ν := by simp only [hL]
        _ ≤ ∑' x, ∫⁻ g in 𝓖, ‖F x g‖ₑ ∂ν :=
          ENNReal.tsum_comp_le_tsum_of_injective hinj (fun x => ∫⁻ g in 𝓖, ‖F x g‖ₑ ∂ν)
        _ < ⊤ := hfin.lt_top
    have hmem : ∀ g, g ∈ S.map Λ.subtype ↔ ∃ h : g ∈ Λ, a ⟨g, h⟩ x₀ = x₀ := by
      intro g
      rw [Subgroup.mem_map]
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨y.2, hy⟩
      · rintro ⟨h, hx⟩
        exact ⟨⟨g, h⟩, hx, rfl⟩
    have h0 := hzero x₀ (S.map Λ.subtype) hmem _ hD hint
    have hs := hasSum_integral_iUnion_ae (fun q => h𝓖.nullMeasurableSet_smul _) hdisj hint
    rw [h0] at hs
    simpa only [hofq, hT] using hs
  let e := selfEquivSigmaOrbitsQuotientStabilizer Λ X
  have h1 : HasSum (T ∘ e.symm) (∑' x, T x) := (e.symm.hasSum_iff).2 hsum.hasSum
  have h2 : HasSum (fun _ : Quotient (orbitRel Λ X) => (0 : ℂ)) (∑' x, T x) := by
    refine h1.sigma fun ω => ?_
    convert horb ω.out using 2 with q
    rfl
  exact h2.unique hasSum_zero

end GlobalTheory
