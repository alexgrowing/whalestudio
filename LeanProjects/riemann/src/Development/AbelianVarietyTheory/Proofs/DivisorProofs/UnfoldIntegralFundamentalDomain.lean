import Mathlib
open MeasureTheory Pointwise

namespace GlobalTheory.UnfoldOrbits

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]

lemma setIntegral_smul_set (μ : Measure G) [μ.IsMulLeftInvariant] (a : G) (s : Set G) (h : G → ℂ) :
    ∫ x in a • s, h x ∂μ = ∫ x in s, h (a * x) ∂μ := by
  rw [← Set.image_smul]
  exact (measurePreserving_mul_left μ a).setIntegral_image_emb
    (MeasurableEquiv.mulLeft a).measurableEmbedding h s

lemma setLIntegral_smul_set (μ : Measure G) [μ.IsMulLeftInvariant] (a : G) (s : Set G) (h : G → ENNReal) :
    ∫⁻ x in a • s, h x ∂μ = ∫⁻ x in s, h (a * x) ∂μ := by
  rw [← Set.image_smul]
  exact ((measurePreserving_mul_left μ a).setLIntegral_comp_emb
    (MeasurableEquiv.mulLeft a).measurableEmbedding h s).symm

lemma tsum_setLIntegral_enorm_mul (μ : Measure G) (𝓕 : Set G) {Q : Type} [Countable Q]
    (T : Q → G → ℂ) (f : G → ℂ) (hTm : ∀ q, AEStronglyMeasurable (T q) μ)
    (hfm : AEStronglyMeasurable f μ) :
    ∑' q, ∫⁻ x in 𝓕, ‖f x * T q x‖ₑ ∂μ = ∫⁻ x in 𝓕, ‖f x‖ₑ * ∑' q, ‖T q x‖ₑ ∂μ := by
  rw [← lintegral_tsum (f := fun q x => ‖f x * T q x‖ₑ) (fun q => ((hfm.mul (hTm q)).restrict).enorm)]
  congr 1
  funext x
  rw [← ENNReal.tsum_mul_left]
  simp only [enorm_mul]

theorem tsum_orbit_eq_zero (Γ : Subgroup G) [Countable Γ] (μ : Measure G) [μ.IsMulLeftInvariant]
    (𝓕 : Set G) {Q : Type} [Countable Q]
    (act : Q → Γ → Q) (T : Q → G → ℂ) (f : G → ℂ)
    (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) (h1 : ∀ q, act q 1 = q)
    (hm : ∀ q a b, act (act q a) b = act q (a * b))
    (hT : ∀ q (δ : Γ) x, T q ((δ : G) * x) = T (act q δ) x) (hTm : ∀ q, AEStronglyMeasurable (T q) μ)
    (hf : ∀ δ ∈ Γ, ∀ x, f (δ * x) = f x) (hfm : AEStronglyMeasurable f μ)
    (hfin : ∫⁻ x in 𝓕, ‖f x‖ₑ * ∑' q, ‖T q x‖ₑ ∂μ ≠ ⊤)
    (hvan : ∀ q (S : Subgroup G), (∀ g, g ∈ S ↔ ∃ hg : g ∈ Γ, act q ⟨g, hg⟩ = q) →
      ∀ D : Set G, IsFundamentalDomain S D μ →
      IntegrableOn (fun x => f x * T q x) D μ → ∫ x in D, f x * T q x ∂μ = 0)
    (q₀ : Q) :
    ∑' q : ({q | ∃ γ, act q₀ γ = q} : Set Q), ∫ x in 𝓕, f x * T q x ∂μ = 0 := by
  classical
  set O : Set Q := {q | ∃ γ, act q₀ γ = q} with hO
  choose γ hγ using (fun q : O => q.2)

  obtain ⟨S, hS⟩ : ∃ S : Subgroup G, ∀ g, g ∈ S ↔ ∃ hg : g ∈ Γ, act q₀ ⟨g, hg⟩ = q₀ := by
    refine ⟨{ carrier := {g | ∃ hg : g ∈ Γ, act q₀ ⟨g, hg⟩ = q₀}
              one_mem' := ⟨Γ.one_mem, h1 q₀⟩
              mul_mem' := ?_
              inv_mem' := ?_ }, fun g => Iff.rfl⟩
    · rintro a b ⟨ha, hqa⟩ ⟨hb, hqb⟩
      refine ⟨Γ.mul_mem ha hb, ?_⟩
      have : (⟨a * b, Γ.mul_mem ha hb⟩ : Γ) = ⟨a, ha⟩ * ⟨b, hb⟩ := rfl
      rw [this, ← hm, hqa, hqb]
    · rintro a ⟨ha, hqa⟩
      refine ⟨Γ.inv_mem ha, ?_⟩
      have : (⟨a⁻¹, Γ.inv_mem ha⟩ : Γ) = (⟨a, ha⟩ : Γ)⁻¹ := rfl
      rw [this]
      conv_lhs => rw [← hqa]
      rw [hm, mul_inv_cancel, h1]
  set D : Set G := ⋃ q : O, (γ q : G) • 𝓕 with hD_def
  have hγinj : Function.Injective γ := fun q q' h => Subtype.ext (by rw [← hγ q, ← hγ q', h])
  have hmeas : ∀ q : O, NullMeasurableSet ((γ q : G) • 𝓕) μ := fun q => h𝓕.nullMeasurableSet_smul (γ q)
  have hdisj : Pairwise (Function.onFun (AEDisjoint μ) fun q : O => (γ q : G) • 𝓕) :=
    fun q q' hne => h𝓕.aedisjoint (hγinj.ne hne)
  have hpt : ∀ (q : O) x, f ((γ q : G) * x) * T q₀ ((γ q : G) * x) = f x * T q x := by
    intro q x
    rw [hf _ (γ q).2, hT, hγ]
  have hchange : ∀ q : O, ∫ x in (γ q : G) • 𝓕, f x * T q₀ x ∂μ = ∫ x in 𝓕, f x * T q x ∂μ := by
    intro q
    rw [setIntegral_smul_set]
    simp only [hpt]
  have hlchange : ∀ q : O,
      ∫⁻ x in (γ q : G) • 𝓕, ‖f x * T q₀ x‖ₑ ∂μ = ∫⁻ x in 𝓕, ‖f x * T q x‖ₑ ∂μ := by
    intro q
    rw [setLIntegral_smul_set]
    simp only [hpt]
  have hint : IntegrableOn (fun x => f x * T q₀ x) D μ := by
    refine ⟨(hfm.mul (hTm q₀)).restrict, ?_⟩
    show ∫⁻ x in D, ‖f x * T q₀ x‖ₑ ∂μ < ⊤
    rw [hD_def, lintegral_iUnion₀ hmeas hdisj]
    simp only [hlchange]
    calc ∑' q : O, ∫⁻ x in 𝓕, ‖f x * T q x‖ₑ ∂μ
        ≤ ∑' q : Q, ∫⁻ x in 𝓕, ‖f x * T q x‖ₑ ∂μ :=
          ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective _
      _ = ∫⁻ x in 𝓕, ‖f x‖ₑ * ∑' q, ‖T q x‖ₑ ∂μ := tsum_setLIntegral_enorm_mul μ 𝓕 T f hTm hfm
      _ < ⊤ := hfin.lt_top
  have hDfd : IsFundamentalDomain S D μ := by
    refine IsFundamentalDomain.mk'' (NullMeasurableSet.iUnion hmeas) ?_ ?_ ?_
    · filter_upwards [h𝓕.ae_covers] with x hx
      obtain ⟨δ, hδ⟩ := hx
      have hq : act q₀ δ⁻¹ ∈ O := ⟨δ⁻¹, rfl⟩
      have hs : ((γ ⟨_, hq⟩ : G) * δ) ∈ S := by
        refine (hS _).2 ⟨Γ.mul_mem (γ ⟨_, hq⟩).2 δ.2, ?_⟩
        have : (⟨(γ ⟨_, hq⟩ : G) * δ, Γ.mul_mem (γ ⟨_, hq⟩).2 δ.2⟩ : Γ) = γ ⟨_, hq⟩ * δ := rfl
        rw [this, ← hm, hγ ⟨_, hq⟩, hm, inv_mul_cancel, h1]
      refine ⟨⟨_, hs⟩, Set.mem_iUnion.2 ⟨⟨_, hq⟩, Set.mem_smul_set.2 ⟨δ • x, hδ, ?_⟩⟩⟩
      show (γ ⟨_, hq⟩ : G) * ((δ : G) * x) = ((γ ⟨_, hq⟩ : G) * δ) * x
      rw [mul_assoc]
    · intro s hs1
      obtain ⟨hsΓ, hsq⟩ := (hS s).1 s.2
      have hsD : s • D = ⋃ q : O, (((⟨s, hsΓ⟩ * γ q : Γ)) : G) • 𝓕 := by
        show (s : G) • D = _
        rw [hD_def, Set.smul_set_iUnion]
        simp only [smul_smul, Subgroup.coe_mul]
      rw [hsD, hD_def, AEDisjoint.iUnion_left_iff]
      intro q
      rw [AEDisjoint.iUnion_right_iff]
      intro q'
      refine h𝓕.aedisjoint (?_ : (⟨s, hsΓ⟩ * γ q : Γ) ≠ γ q')
      intro heq
      have hqq : q = q' := by
        apply Subtype.ext
        rw [← hγ q, ← hγ q', ← heq, ← hm, hsq]
      subst hqq
      apply hs1
      have h1' : (⟨s, hsΓ⟩ : Γ) = 1 := by
        simpa using heq
      exact Subtype.ext (congrArg Subtype.val h1' : (s : G) = 1)
    · intro s
      exact (measurePreserving_mul_left μ (s : G)).quasiMeasurePreserving
  have hzero := hvan q₀ S hS D hDfd hint
  rw [hD_def, integral_iUnion_ae hmeas hdisj (hD_def ▸ hint)] at hzero
  simpa only [hchange] using hzero

end GlobalTheory.UnfoldOrbits

namespace GlobalTheory.UnfoldOrbits

theorem integral_mul_tsum_eq_zero : ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    (Γ : Subgroup G) [Countable Γ] (μ : Measure G) [μ.IsMulLeftInvariant] (𝓕 : Set G) (Q : Type) [Countable Q]
    (act : Q → Γ → Q) (T : Q → G → ℂ) (f : G → ℂ),
    IsFundamentalDomain Γ 𝓕 μ → (∀ q, act q 1 = q) → (∀ q a b, act (act q a) b = act q (a * b)) →
    (∀ q (δ : Γ) x, T q ((δ : G) * x) = T (act q δ) x) → (∀ q, AEStronglyMeasurable (T q) μ) →
    (∀ δ ∈ Γ, ∀ x, f (δ * x) = f x) → AEStronglyMeasurable f μ →
    ∫⁻ x in 𝓕, ‖f x‖ₑ * ∑' q, ‖T q x‖ₑ ∂μ ≠ ⊤ →
    (∀ q (S : Subgroup G), (∀ g, g ∈ S ↔ ∃ hg : g ∈ Γ, act q ⟨g, hg⟩ = q) → ∀ D : Set G, IsFundamentalDomain S D μ →
      IntegrableOn (fun x => f x * T q x) D μ → ∫ x in D, f x * T q x ∂μ = 0) →
    ∫ x in 𝓕, f x * ∑' q, T q x ∂μ = 0 := by
  intro G _ _ _ _ _ Γ _ μ _ 𝓕 Q _ act T f h𝓕 h1 hm hT hTm hf hfm hfin hvan
  classical
  have hL := tsum_setLIntegral_enorm_mul μ 𝓕 T f hTm hfm
  have hfin' : ∑' q, ∫⁻ x in 𝓕, ‖f x * T q x‖ₑ ∂μ ≠ ⊤ := by rw [hL]; exact hfin
  have e1 : ∫ x in 𝓕, f x * ∑' q, T q x ∂μ = ∑' q, ∫ x in 𝓕, f x * T q x ∂μ := by
    simp_rw [← tsum_mul_left]
    exact integral_tsum (fun q => (hfm.mul (hTm q)).restrict) hfin'
  have hsum : Summable (fun q => ∫ x in 𝓕, f x * T q x ∂μ) := by
    refine Summable.of_norm_bounded (ENNReal.summable_toReal hfin') (fun q => ?_)
    refine (norm_integral_le_lintegral_norm _).trans (le_of_eq ?_)
    simp only [ofReal_norm]
  rw [e1]

  let g : Q → Set Q := fun q => {q' | ∃ γ, act q γ = q'}
  have hfib : ∀ q₀, g ⁻¹' {g q₀} = g q₀ := by
    intro q₀
    ext q
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro h
      have : q ∈ g q := ⟨1, h1 q⟩
      rwa [h] at this
    · rintro ⟨γ, rfl⟩
      ext q'
      constructor
      · rintro ⟨δ, rfl⟩
        exact ⟨γ * δ, (hm _ _ _).symm⟩
      · rintro ⟨δ, rfl⟩
        refine ⟨γ⁻¹ * δ, ?_⟩
        show act (act q₀ γ) (γ⁻¹ * δ) = act q₀ δ
        rw [hm, mul_inv_cancel_left]
  have H := hsum.hasSum.tsum_fiberwise g
  have H0 : (fun c => ∑' b : ↑(g ⁻¹' {c}), ∫ x in 𝓕, f x * T b x ∂μ) = fun _ => 0 := by
    funext c
    by_cases hc : ∃ q₀, g q₀ = c
    · obtain ⟨q₀, rfl⟩ := hc
      rw [hfib q₀]
      exact tsum_orbit_eq_zero Γ μ 𝓕 act T f h𝓕 h1 hm hT hTm hf hfm hfin hvan q₀
    · have : g ⁻¹' {c} = ∅ := by
        ext q
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
        exact fun h => hc ⟨q, h⟩
      rw [this]
      simp
  rw [H0] at H
  exact H.unique hasSum_zero

end GlobalTheory.UnfoldOrbits
