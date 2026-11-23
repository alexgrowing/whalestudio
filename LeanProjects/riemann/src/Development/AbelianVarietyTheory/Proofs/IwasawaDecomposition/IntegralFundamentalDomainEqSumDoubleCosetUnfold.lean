import Mathlib
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.IntegralFundamentalDomainEqSumDoubleCoset
open MeasureTheory
open scoped InnerProductSpace

namespace GlobalTheory.Unfold

theorem tsum_indicator_coset_complex {G : Type} [Group G] (Γ K : Subgroup G) (a : G)
    (hfin : {γ : G | γ ∈ Γ ∧ a⁻¹ * γ * a ∈ K}.Finite) (x : G) :
    ∑' γ : Γ, ((fun y => a⁻¹ * y) ⁻¹' (K : Set G)).indicator (1 : G → ℂ) (γ • x)
      = ({γ : G | γ ∈ Γ ∧ a⁻¹ * γ * a ∈ K}.ncard : ℂ) *
        {x : G | ∃ γ ∈ Γ, ∃ k ∈ K, x = γ * a * k}.indicator 1 x := by
  have h := congrArg ENNReal.toReal (GlobalTheory.Ker.tsum_indicator_coset Γ K a hfin x)
  rw [ENNReal.tsum_toReal_eq (fun γ => by
    by_cases hγ : γ • x ∈ (fun y => a⁻¹ * y) ⁻¹' (K : Set G)
    · rw [Set.indicator_of_mem hγ]; simp
    · rw [Set.indicator_of_notMem hγ]; simp)] at h
  have h2 := congrArg (fun r : ℝ => (r : ℂ)) h
  simp only [Complex.ofReal_tsum] at h2
  convert h2 using 1
  · congr 1; funext γ
    by_cases hγ : γ • x ∈ (fun y => a⁻¹ * y) ⁻¹' (K : Set G)
    · rw [Set.indicator_of_mem hγ, Set.indicator_of_mem hγ]; simp
    · rw [Set.indicator_of_notMem hγ, Set.indicator_of_notMem hγ]; simp
  · by_cases hx : x ∈ {x : G | ∃ γ ∈ Γ, ∃ k ∈ K, x = γ * a * k}
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]; simp
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]; simp

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
  [BorelSpace G]

theorem unfold_coset (ν : Measure G) [ν.IsMulLeftInvariant] (Γ K : Subgroup G)
    [Countable Γ] (𝓖 : Set G) (h𝓖 : IsFundamentalDomain Γ 𝓖 ν) (hK : IsOpen (K : Set G)) (a : G)
    (hfin : {γ : G | γ ∈ Γ ∧ a⁻¹ * γ * a ∈ K}.Finite) (f : G → ℂ)
    (hfl : ∀ γ ∈ Γ, ∀ x, f (γ * x) = f x)
    (hf : IntegrableOn f ((fun y => a⁻¹ * y) ⁻¹' (K : Set G)) ν) :
    IntegrableOn f {x : G | ∃ γ ∈ Γ, ∃ k ∈ K, x = γ * a * k} (ν.restrict 𝓖) ∧
    ({γ : G | γ ∈ Γ ∧ a⁻¹ * γ * a ∈ K}.ncard : ℂ) *
      ∫ x in {x : G | ∃ γ ∈ Γ, ∃ k ∈ K, x = γ * a * k}, f x ∂(ν.restrict 𝓖)
      = ∫ x in (fun y => a⁻¹ * y) ⁻¹' (K : Set G), f x ∂ν := by
  set A := (fun y => a⁻¹ * y) ⁻¹' (K : Set G) with hAdef
  set C := {x : G | ∃ γ ∈ Γ, ∃ k ∈ K, x = γ * a * k} with hCdef
  set n := {γ : G | γ ∈ Γ ∧ a⁻¹ * γ * a ∈ K}.ncard with hndef
  have hA : MeasurableSet A := (hK.preimage (continuous_const.mul continuous_id)).measurableSet
  have hC : MeasurableSet C := (GlobalTheory.Ker.isOpen_doubleCoset_of_isOpen Γ K hK a).measurableSet
  have hn : n ≠ 0 := ((Set.ncard_pos hfin).2 ⟨1, Γ.one_mem, by simpa using K.one_mem⟩).ne'
  have hcount : ∀ x, ∑' γ : Γ, A.indicator (1 : G → ENNReal) (γ • x) = (n : ENNReal) * C.indicator 1 x :=
    GlobalTheory.Ker.tsum_indicator_coset Γ K a hfin
  have hcountC : ∀ x, ∑' γ : Γ, A.indicator (1 : G → ℂ) (γ • x) = (n : ℂ) * C.indicator 1 x :=
    tsum_indicator_coset_complex Γ K a hfin
  have hφ : Integrable (A.indicator f) ν := hf.integrable_indicator hA
  have hpt : ∀ (γ : Γ) x, A.indicator f (γ • x) = A.indicator (1 : G → ℂ) (γ • x) * f x := by
    intro γ x
    have : f (γ • x) = f x := hfl γ γ.2 x
    by_cases hx : γ • x ∈ A
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, Pi.one_apply, one_mul, this]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, zero_mul]
  have hptE : ∀ (γ : Γ) x,
      ‖A.indicator f (γ • x)‖ₑ = A.indicator (1 : G → ENNReal) (γ • x) * ‖f x‖ₑ := by
    intro γ x
    have : f (γ • x) = f x := hfl γ γ.2 x
    by_cases hx : γ • x ∈ A
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, Pi.one_apply, one_mul, this]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, zero_mul, enorm_zero]
  have hmeasγ : ∀ γ : Γ, AEStronglyMeasurable (fun x => A.indicator f (γ • x)) (ν.restrict 𝓖) := by
    intro γ
    exact (hφ.aestronglyMeasurable.comp_quasiMeasurePreserving
      (measurePreserving_smul γ ν).quasiMeasurePreserving).restrict
  have hlin : ∑' γ : Γ, ∫⁻ x in 𝓖, ‖A.indicator f (γ • x)‖ₑ ∂ν = ∫⁻ x, ‖A.indicator f x‖ₑ ∂ν :=
    (h𝓖.lintegral_eq_tsum'' (fun x => ‖A.indicator f x‖ₑ)).symm
  have hlin2 : ∑' γ : Γ, ∫⁻ x in 𝓖, ‖A.indicator f (γ • x)‖ₑ ∂ν
      = (n : ENNReal) * ∫⁻ x in C, ‖f x‖ₑ ∂(ν.restrict 𝓖) := by
    rw [← lintegral_tsum (fun γ => (hmeasγ γ).enorm)]
    simp_rw [hptE, ENNReal.tsum_mul_right, hcount]
    rw [← lintegral_indicator hC, ← lintegral_const_mul' _ _ (ENNReal.natCast_ne_top n)]
    refine lintegral_congr fun x => ?_
    by_cases hx : x ∈ C
    · simp [Set.indicator_of_mem hx, hndef]
    · simp [Set.indicator_of_notMem hx]
  have hCU : C = ⋃ γ : Γ, (fun x => (γ : G) * x) ⁻¹' A := by
    ext x
    simp only [hCdef, hAdef, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_preimage, SetLike.mem_coe]
    constructor
    · rintro ⟨γ, hγ, k, hk, rfl⟩
      refine ⟨⟨γ⁻¹, Γ.inv_mem hγ⟩, ?_⟩
      have : a⁻¹ * (γ⁻¹ * (γ * a * k)) = k := by group
      simpa [this] using hk
    · rintro ⟨γ, hγ⟩
      exact ⟨(γ : G)⁻¹, Γ.inv_mem γ.2, _, hγ, by group⟩
  have hintγ : ∀ γ : Γ, IntegrableOn f ((fun x => (γ : G) * x) ⁻¹' A) ν := by
    intro γ
    have := ((measurePreserving_mul_left ν (γ : G)).integrableOn_comp_preimage
      (measurableEmbedding_mulLeft (γ : G)) (f := f) (s := A)).2 hf
    have hfeq : f ∘ (fun x => (γ : G) * x) = f := funext fun x => hfl γ γ.2 x
    rwa [hfeq] at this
  have hmeasC : AEStronglyMeasurable f ((ν.restrict 𝓖).restrict C) := by
    have : AEStronglyMeasurable f (ν.restrict C) := by
      rw [hCU, aestronglyMeasurable_iUnion_iff]
      exact fun γ => (hintγ γ).aestronglyMeasurable
    exact this.mono_measure (Measure.restrict_mono subset_rfl Measure.restrict_le_self)
  have hfinC : ∫⁻ x in C, ‖f x‖ₑ ∂(ν.restrict 𝓖) ≠ ⊤ := by
    intro htop
    have h1 := hlin2.symm.trans hlin
    rw [htop, ENNReal.mul_top (by exact_mod_cast hn)] at h1
    exact hφ.hasFiniteIntegral.ne h1.symm
  have hintC : IntegrableOn f C (ν.restrict 𝓖) := ⟨hmeasC, hfinC.lt_top⟩
  refine ⟨hintC, ?_⟩
  rw [← integral_indicator hA, h𝓖.integral_eq_tsum'' _ hφ,
    ← integral_tsum hmeasγ (by rw [hlin]; exact hφ.hasFiniteIntegral.ne)]
  simp_rw [hpt, tsum_mul_right, hcountC]
  rw [← integral_indicator hC, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  by_cases hx : x ∈ C
  · simp [Set.indicator_of_mem hx, hndef]
  · simp [Set.indicator_of_notMem hx]

end GlobalTheory.Unfold

namespace GlobalTheory.Unfold

theorem integral_fundamentalDomain_eq_sum_unfold : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] (ν : Measure G) [ν.IsMulLeftInvariant] (Γ Ω : Subgroup G) [Countable Γ] (𝓖 : Set G), IsFundamentalDomain Γ 𝓖 ν → IsOpen (Ω : Set G) → ∀ (ι : Type) [Fintype ι] (h : ι → G), (∀ x : G, ∃! i, ∃ γ ∈ Γ, ∃ k ∈ Ω, x = γ * h i * k) → (∀ i, {γ : G | γ ∈ Γ ∧ (h i)⁻¹ * γ * h i ∈ Ω}.Finite) → ∀ f : G → ℂ, (∀ γ ∈ Γ, ∀ x, f (γ * x) = f x) → (∀ i, IntegrableOn (fun k => f (h i * k)) Ω ν) → IntegrableOn f 𝓖 ν ∧ ∫ x in 𝓖, f x ∂ν = ∑ i, (({γ : G | γ ∈ Γ ∧ (h i)⁻¹ * γ * h i ∈ Ω}.ncard : ℕ) : ℂ)⁻¹ * ∫ k in (Ω : Set G), f (h i * k) ∂ν := by
  intro G _ _ _ _ _ ν _ Γ Ω _ 𝓖 h𝓖 hΩ ι _ h huniq hfin f hfl hf
  set C : ι → Set G := fun i => {x : G | ∃ γ ∈ Γ, ∃ k ∈ Ω, x = γ * h i * k} with hCdef
  have hC : ∀ i, MeasurableSet (C i) := fun i =>
    (GlobalTheory.Ker.isOpen_doubleCoset_of_isOpen Γ Ω hΩ (h i)).measurableSet
  have hpos : ∀ i, {γ : G | γ ∈ Γ ∧ (h i)⁻¹ * γ * h i ∈ Ω}.ncard ≠ 0 := fun i =>
    ((Set.ncard_pos (hfin i)).2 ⟨1, Γ.one_mem, by simpa using Ω.one_mem⟩).ne'
  have hpre : ∀ i, (fun y => h i * y) ⁻¹' ((fun y => (h i)⁻¹ * y) ⁻¹' (Ω : Set G)) = Ω := by
    intro i; ext k; simp
  have hA : ∀ i, IntegrableOn f ((fun y => (h i)⁻¹ * y) ⁻¹' (Ω : Set G)) ν := by
    intro i
    refine ((measurePreserving_mul_left ν (h i)).integrableOn_comp_preimage
      (measurableEmbedding_mulLeft (h i))).1 ?_
    rw [hpre]; exact hf i
  have hAint : ∀ i, ∫ x in (fun y => (h i)⁻¹ * y) ⁻¹' (Ω : Set G), f x ∂ν
      = ∫ k in (Ω : Set G), f (h i * k) ∂ν := by
    intro i
    have := (measurePreserving_mul_left ν (h i)).setIntegral_preimage_emb
      (measurableEmbedding_mulLeft (h i)) f ((fun y => (h i)⁻¹ * y) ⁻¹' (Ω : Set G))
    rw [hpre] at this
    exact this.symm
  have hU := fun i => unfold_coset ν Γ Ω 𝓖 h𝓖 hΩ (h i) (hfin i) f hfl (hA i)
  have hF : f = fun x => ∑ i, (C i).indicator f x := by
    funext x
    obtain ⟨i, hi, hu⟩ := huniq x
    rw [Finset.sum_eq_single i]
    · rw [Set.indicator_of_mem (show x ∈ C i from hi)]
    · intro j _ hj
      exact Set.indicator_of_notMem (s := C j) (fun hx => hj (hu j hx)) f
    · intro hi; exact absurd (Finset.mem_univ i) hi
  have hint : ∀ i, Integrable ((C i).indicator f) (ν.restrict 𝓖) := fun i =>
    (integrable_indicator_iff (hC i)).2 (hU i).1
  refine ⟨?_, ?_⟩
  · rw [IntegrableOn, hF]
    exact integrable_finset_sum _ fun i _ => hint i
  · have h1 : ∫ x in 𝓖, f x ∂ν = ∫ x in 𝓖, ∑ i, (C i).indicator f x ∂ν := by
      conv_lhs => rw [hF]
    rw [h1, integral_finset_sum _ fun i _ => hint i]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_indicator (hC i), ← hAint i, ← (hU i).2]
    have : (({γ : G | γ ∈ Γ ∧ (h i)⁻¹ * γ * h i ∈ Ω}.ncard : ℕ) : ℂ) ≠ 0 := by
      exact_mod_cast hpos i
    rw [← mul_assoc, inv_mul_cancel₀ this, one_mul]

end GlobalTheory.Unfold
