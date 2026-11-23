import Mathlib
import GroundTheory.GlobalFields.TateThesis.AdelePoisson

namespace GroundTheory.Global

open NumberField NumberField.mixedEmbedding IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
  MeasureTheory Filter Topology
open scoped NumberField.AdeleRing SchwartzMap Classical nonZeroDivisors Pointwise

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

theorem exists_mul_mem_integralFiniteAdeles_of_isCompact {S : Set 𝔸ᶠ[K]} (hS : IsCompact S) :
    ∃ d : 𝓞 K, d ≠ 0 ∧ ∀ s ∈ S,
      algebraMap K 𝔸ᶠ[K] (algebraMap (𝓞 K) K d) * s ∈ integralFiniteAdeles (𝓞 K) K := by
  have hint : ∀ r : 𝓞 K,
      algebraMap K 𝔸ᶠ[K] (algebraMap (𝓞 K) K r) ∈ integralFiniteAdeles (𝓞 K) K :=
    fun r v ↦ coe_algebraMap_mem_adicCompletionIntegers v r
  let U : {d : 𝓞 K // d ≠ 0} → Set 𝔸ᶠ[K] := fun d ↦
    {s | algebraMap K 𝔸ᶠ[K] (algebraMap (𝓞 K) K d.1) * s ∈ integralFiniteAdeles (𝓞 K) K}
  have hUo : ∀ d, IsOpen (U d) := fun d ↦
    isOpen_integralFiniteAdeles.preimage (continuous_const_mul _)
  have hsU : S ⊆ ⋃ d, U d := by
    intro s _
    obtain ⟨k, hk⟩ := exists_sub_mem_integralFiniteAdeles (R := 𝓞 K) s
    obtain ⟨n, m, hm, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) k
    have hm0 : m ≠ 0 := nonZeroDivisors.ne_zero hm
    have hmK : algebraMap (𝓞 K) K m ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr hm0
    refine Set.mem_iUnion.mpr ⟨⟨m, hm0⟩, ?_⟩
    have h : algebraMap K 𝔸ᶠ[K] (algebraMap (𝓞 K) K m) * s =
        algebraMap K 𝔸ᶠ[K] (algebraMap (𝓞 K) K n) + algebraMap K 𝔸ᶠ[K] (algebraMap (𝓞 K) K m) *
          (s - algebraMap K 𝔸ᶠ[K] (algebraMap (𝓞 K) K n / algebraMap (𝓞 K) K m)) := by
      rw [mul_sub, ← map_mul, mul_div_cancel₀ _ hmK]
      ring
    show algebraMap K 𝔸ᶠ[K] (algebraMap (𝓞 K) K m) * s ∈ integralFiniteAdeles (𝓞 K) K
    rw [h]
    exact add_mem (hint n) (mul_mem (hint m) hk)
  have hdU : Directed (· ⊆ ·) U := by
    intro d e
    refine ⟨⟨d.1 * e.1, mul_ne_zero d.2 e.2⟩, fun s hs ↦ ?_, fun s hs ↦ ?_⟩
    · have := mul_mem (hint e.1) hs
      show algebraMap K 𝔸ᶠ[K] (algebraMap (𝓞 K) K (d.1 * e.1)) * s ∈ integralFiniteAdeles (𝓞 K) K
      rwa [map_mul, map_mul, mul_comm (algebraMap K 𝔸ᶠ[K] (algebraMap (𝓞 K) K d.1)), mul_assoc]
    · have := mul_mem (hint d.1) hs
      show algebraMap K 𝔸ᶠ[K] (algebraMap (𝓞 K) K (d.1 * e.1)) * s ∈ integralFiniteAdeles (𝓞 K) K
      rwa [map_mul, map_mul, mul_assoc]
  have : Nonempty {d : 𝓞 K // d ≠ 0} := ⟨⟨1, one_ne_zero⟩⟩
  obtain ⟨d, hd⟩ := hS.elim_directed_cover U hUo hsU hdU
  exact ⟨d.1, d.2, fun s hs ↦ hd hs⟩

theorem summable_ite_mem_of_summable_idealLattice (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {h : mixedSpace K → ℝ} (hh : Summable fun α : idealLattice K J ↦ h α) :
    Summable fun ξ : K ↦
      if ξ ∈ (J : FractionalIdeal (𝓞 K)⁰ K) then h (mixedEmbedding K ξ) else 0 := by
  set e := idealLatticeEquiv J
  let g : idealLattice K J → K := fun α ↦ ((e.symm α : _) : K)
  have hinj : Function.Injective g := fun α β hαβ ↦ e.symm.injective (Subtype.ext hαβ)
  have hsupp : ∀ ξ ∉ Set.range g,
      (if ξ ∈ (J : FractionalIdeal (𝓞 K)⁰ K) then h (mixedEmbedding K ξ) else 0) = 0 := by
    intro ξ hξ
    rw [if_neg]
    intro hm
    exact hξ ⟨e ⟨ξ, hm⟩, by simp [g]⟩
  rw [← hinj.summable_iff hsupp]
  convert hh using 1
  funext α
  simp only [Function.comp_apply, g]
  rw [if_pos (show ((e.symm α : _) : K) ∈ (J : FractionalIdeal (𝓞 K)⁰ K) from (e.symm α).2)]
  have he := coe_idealLatticeEquiv J (e.symm α)
  rw [Equiv.apply_symm_apply] at he
  rw [he]

theorem summable_inv_one_add_norm_pow_idealLattice (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    Summable fun α : idealLattice K J ↦
      ((1 + ‖(α : mixedSpace K)‖) ^ (Module.finrank ℤ (idealLattice K J) + 1))⁻¹ := by
  have hs := ZLattice.summable_norm_pow_inv (L := idealLattice K J)
    (Module.finrank ℤ (idealLattice K J) + 1) (by omega)
  refine Summable.of_norm_bounded_eventually hs ?_
  filter_upwards [(Set.finite_singleton (0 : idealLattice K J)).compl_mem_cofinite] with ℓ hℓ
  have hpos : 0 < ‖ℓ‖ := norm_pos_iff.mpr hℓ
  rw [Real.norm_of_nonneg (by positivity), inv_pow]
  gcongr
  change ‖ℓ‖ ≤ 1 + ‖ℓ‖
  linarith

theorem exists_summable_bound_tensor_cosetIndicator (φ : 𝓢(mixedSpace K, ℂ))
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (b : 𝔸ᶠ[K]) {C : Set (IdeleGroup K)} (hC : IsCompact C) :
    ∃ u : K → ℝ, Summable u ∧ ∀ a ∈ C, ∀ ξ : K,
      ‖schwartzBruhatTensor φ (cosetIndicator I b) (a • algebraMap K 𝔸[K] ξ)‖ ≤ u ξ := by

  set S : Set 𝔸ᶠ[K] := (fun p : IdeleGroup K × 𝔸ᶠ[K] ↦
      ((IdeleGroup.toFinite K p.1⁻¹ : (𝔸ᶠ[K])ˣ) : 𝔸ᶠ[K]) * p.2) ''
    (C ×ˢ (b +ᵥ (idealFiniteAdeles I : Set 𝔸ᶠ[K])))
  have hS : IsCompact S := (hC.prod ((isCompact_idealFiniteAdeles I).vadd b)).image
    ((Units.continuous_val.comp ((IdeleGroup.continuous_toFinite (K := K)).comp
      (continuous_inv.comp continuous_fst))).mul continuous_snd)
  obtain ⟨d, hd0, hd⟩ := exists_mul_mem_integralFiniteAdeles_of_isCompact hS
  set dK := algebraMap (𝓞 K) K d
  have hdK : dK ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr hd0
  set J : (FractionalIdeal (𝓞 K)⁰ K)ˣ := Units.mk0 (FractionalIdeal.spanSingleton (𝓞 K)⁰ dK⁻¹)
    ((FractionalIdeal.spanSingleton_ne_zero_iff).mpr (inv_ne_zero hdK))
  have hJ : ∀ a ∈ C, ∀ ξ : K,
      ((IdeleGroup.toFinite K a : (𝔸ᶠ[K])ˣ) : 𝔸ᶠ[K]) * algebraMap K 𝔸ᶠ[K] ξ - b ∈
        idealFiniteAdeles I → ξ ∈ (J : FractionalIdeal (𝓞 K)⁰ K) := by
    intro a ha ξ hξ
    have hmem : algebraMap K 𝔸ᶠ[K] ξ ∈ S := by
      refine ⟨(a, ((IdeleGroup.toFinite K a : (𝔸ᶠ[K])ˣ) : 𝔸ᶠ[K]) * algebraMap K 𝔸ᶠ[K] ξ),
        ⟨ha, mem_vadd_idealFiniteAdeles.mpr hξ⟩, ?_⟩
      simp only [map_inv, Units.inv_mul_cancel_left]
    have h1 := hd _ hmem
    rw [← map_mul] at h1
    have h2 : dK * ξ ∈ ((1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) := by
      rw [← algebraMap_mem_idealFiniteAdeles_iff, ← SetLike.mem_coe, idealFiniteAdeles_one]
      exact h1
    rw [Units.val_one] at h2
    obtain ⟨r, hr⟩ := (FractionalIdeal.mem_one_iff _).mp h2
    refine (FractionalIdeal.mem_spanSingleton _).mpr ⟨r, ?_⟩
    rw [Algebra.smul_def, hr, mul_comm dK, mul_assoc, mul_inv_cancel₀ hdK, mul_one]

  set k := Module.finrank ℤ (idealLattice K J) + 1
  obtain ⟨A, hA, hφ⟩ := exists_norm_le_inv_one_add_pow φ k
  have hcont : Continuous fun a : IdeleGroup K ↦ ‖homeomorphMixedSpace K
      ((IdeleGroup.toInfinite K a⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K)‖ :=
    continuous_norm.comp ((homeomorphMixedSpace K).continuous.comp (Units.continuous_val.comp
      ((IdeleGroup.continuous_toInfinite (K := K)).comp continuous_inv)))
  obtain ⟨B, hB⟩ := hC.exists_bound_of_continuousOn hcont.continuousOn
  set B' := max B 1
  have hB'1 : 1 ≤ B' := le_max_right _ _
  have hB'0 : 0 < B' := zero_lt_one.trans_le hB'1
  refine ⟨fun ξ ↦ if ξ ∈ (J : FractionalIdeal (𝓞 K)⁰ K) then
      A * B' ^ k * ((1 + ‖mixedEmbedding K ξ‖) ^ k)⁻¹ else 0, ?_, ?_⟩
  · exact summable_ite_mem_of_summable_idealLattice J
      (h := fun x ↦ A * B' ^ k * ((1 + ‖x‖) ^ k)⁻¹)
      ((summable_inv_one_add_norm_pow_idealLattice J).mul_left (A * B' ^ k))
  intro a ha ξ
  set c := homeomorphMixedSpace K
    ((IdeleGroup.toInfinite K a : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K)
  set c' := homeomorphMixedSpace K
    ((IdeleGroup.toInfinite K a⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K)
  have hcc : c' * c = 1 := by
    rw [← homeomorphMixedSpace_mul, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one,
      Units.val_one, homeomorphMixedSpace_apply, map_one]
  have hval : schwartzBruhatTensor φ (cosetIndicator I b) (a • algebraMap K 𝔸[K] ξ) =
      φ (c * mixedEmbedding K ξ) * cosetIndicator I b
        (((IdeleGroup.toFinite K a : (𝔸ᶠ[K])ˣ) : 𝔸ᶠ[K]) * algebraMap K 𝔸ᶠ[K] ξ) := by
    have h1 : (a • algebraMap K 𝔸[K] ξ).1 = ((IdeleGroup.toInfinite K a : (InfiniteAdeleRing K)ˣ) :
        InfiniteAdeleRing K) * algebraMap K (InfiniteAdeleRing K) ξ := rfl
    have h2 : (a • algebraMap K 𝔸[K] ξ).2 =
        ((IdeleGroup.toFinite K a : (𝔸ᶠ[K])ˣ) : 𝔸ᶠ[K]) * algebraMap K 𝔸ᶠ[K] ξ := rfl
    simp only [schwartzBruhatTensor]
    rw [h1, h2, homeomorphMixedSpace_mul, homeomorphMixedSpace_algebraMap]
  rw [hval, cosetIndicator_apply]
  beta_reduce
  split_ifs with hm hJm hJm
  · rw [mul_one]
    set x := mixedEmbedding K ξ
    have hx : ‖x‖ ≤ B' * ‖c * x‖ := by
      calc ‖x‖ = ‖c' * (c * x)‖ := by rw [← mul_assoc, hcc, one_mul]
        _ ≤ ‖c'‖ * ‖c * x‖ := norm_mul_le _ _
        _ ≤ B' * ‖c * x‖ := by
          gcongr
          exact ((norm_norm _).symm.trans_le (hB a ha)).trans (le_max_left _ _)
    have key : 1 + ‖x‖ ≤ B' * (1 + ‖c * x‖) := by nlinarith [norm_nonneg (c * x)]
    calc ‖φ (c * x)‖ ≤ A * ((1 + ‖c * x‖) ^ k)⁻¹ := hφ _
      _ = A * (B' ^ k * ((B' * (1 + ‖c * x‖)) ^ k)⁻¹) := by
          rw [mul_pow, mul_inv, ← mul_assoc (B' ^ k), mul_inv_cancel₀ (by positivity), one_mul]
      _ ≤ A * (B' ^ k * ((1 + ‖x‖) ^ k)⁻¹) := by gcongr
      _ = A * B' ^ k * ((1 + ‖x‖) ^ k)⁻¹ := by ring
  · exact absurd (hJ a ha ξ hm) hJm
  · rw [mul_zero, norm_zero]
    positivity
  · rw [mul_zero, norm_zero]

theorem exists_summable_bound_smul_algebraMap {F : 𝔸[K] → ℂ} (hF : F ∈ schwartzBruhat K)
    {C : Set (IdeleGroup K)} (hC : IsCompact C) :
    ∃ u : K → ℝ, Summable u ∧ ∀ a ∈ C, ∀ ξ : K, ‖F (a • algebraMap K 𝔸[K] ξ)‖ ≤ u ξ := by
  have hF' := schwartzBruhat_le_span_cosetIndicator hF
  clear hF
  induction hF' using Submodule.span_induction with
  | mem G hG =>
    obtain ⟨φ, I, b, rfl⟩ := hG
    exact exists_summable_bound_tensor_cosetIndicator φ I b hC
  | zero => exact ⟨0, summable_zero, fun _ _ _ ↦ by simp⟩
  | add G H _ _ hG hH =>
    obtain ⟨u, hu, hGu⟩ := hG
    obtain ⟨w, hw, hHw⟩ := hH
    exact ⟨u + w, hu.add hw, fun a ha ξ ↦ (norm_add_le _ _).trans (add_le_add (hGu a ha ξ) (hHw a ha ξ))⟩
  | smul r G _ hG =>
    obtain ⟨u, hu, hGu⟩ := hG
    refine ⟨fun ξ ↦ ‖r‖ * u ξ, hu.mul_left _, fun a ha ξ ↦ ?_⟩
    rw [Pi.smul_apply, smul_eq_mul, norm_mul]
    exact mul_le_mul_of_nonneg_left (hGu a ha ξ) (norm_nonneg r)

theorem tendstoUniformlyOn_tsum_smul_algebraMap {F : 𝔸[K] → ℂ} (hF : F ∈ schwartzBruhat K)
    {C : Set (IdeleGroup K)} (hC : IsCompact C) :
    TendstoUniformlyOn (fun (s : Finset K) (a : IdeleGroup K) ↦ ∑ ξ ∈ s, F (a • algebraMap K 𝔸[K] ξ))
      (fun a ↦ ∑' ξ : K, F (a • algebraMap K 𝔸[K] ξ)) atTop C := by
  obtain ⟨u, hu, hFu⟩ := exists_summable_bound_smul_algebraMap hF hC
  exact tendstoUniformlyOn_tsum hu fun ξ a ha ↦ hFu a ha ξ

theorem exists_summable_bound_adelicFourier_inv_smul_algebraMap {F : 𝔸[K] → ℂ}
    (hF : F ∈ schwartzBruhat K) {C : Set (IdeleGroup K)} (hC : IsCompact C) :
    ∃ u : K → ℝ, Summable u ∧ ∀ a ∈ C, ∀ ξ : K,
      ‖adelicFourier K F (a⁻¹ • algebraMap K 𝔸[K] ξ)‖ ≤ u ξ := by
  obtain ⟨u, hu, hFu⟩ := exists_summable_bound_smul_algebraMap
    (adelicFourier_mem_schwartzBruhat hF) hC.inv
  exact ⟨u, hu, fun a ha ξ ↦ hFu a⁻¹ (Set.inv_mem_inv.mpr ha) ξ⟩

theorem tendstoUniformlyOn_tsum_adelicFourier_inv_smul_algebraMap {F : 𝔸[K] → ℂ}
    (hF : F ∈ schwartzBruhat K) {C : Set (IdeleGroup K)} (hC : IsCompact C) :
    TendstoUniformlyOn (fun (s : Finset K) (a : IdeleGroup K) ↦
        ∑ ξ ∈ s, adelicFourier K F (a⁻¹ • algebraMap K 𝔸[K] ξ))
      (fun a ↦ ∑' ξ : K, adelicFourier K F (a⁻¹ • algebraMap K 𝔸[K] ξ)) atTop C := by
  obtain ⟨u, hu, hFu⟩ := exists_summable_bound_adelicFourier_inv_smul_algebraMap hF hC
  exact tendstoUniformlyOn_tsum hu fun ξ a ha ↦ hFu a ha ξ

end

end GroundTheory.Global
