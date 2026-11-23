import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.RankOneEisenstein.Theta2Integral
import GroundTheory.GlobalFields.TateThesis.TateThetaDecay
set_option maxSynthPendingDepth 1

open NumberField NumberField.mixedEmbedding IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
  Matrix MeasureTheory Filter Topology
open scoped NumberField.AdeleRing SchwartzMap Classical nonZeroDivisors Pointwise
open PositivityTheory.EisRk1 GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Adele2
  GroundTheory.Automorphic.GodementSection IdeleGroup

set_option synthInstance.maxSize 1000

namespace GlobalTheory.CompanionTheory.EisRk1

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

def infC (a : 𝔸[K]) : mixedSpace K := homeomorphMixedSpace K a.1

theorem infC_mul (a b : 𝔸[K]) : infC (a * b) = infC a * infC b :=
  homeomorphMixedSpace_mul _ _

theorem infC_add (a b : 𝔸[K]) : infC (a + b) = infC a + infC b := by
  simp only [infC, homeomorphMixedSpace_apply]
  exact map_add (InfiniteAdeleRing.ringEquiv_mixedSpace K) a.1 b.1

theorem infC_algebraMap (x : K) : infC (algebraMap K 𝔸[K] x) = mixedEmbedding K x := by
  simp only [infC, adeleRing_algebraMap_fst, homeomorphMixedSpace_algebraMap]

theorem continuous_infC : Continuous (infC (K := K)) :=
  (homeomorphMixedSpace K).continuous.comp continuous_fst

theorem exists_ideal_of_isCompact {S : Set 𝔸ᶠ[K]} (hS : IsCompact S) :
    ∃ (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (κ₀ : ℝ), 0 < κ₀ ∧
      (∀ ξ : K, algebraMap K 𝔸ᶠ[K] ξ ∈ S → ξ ∈ (J : FractionalIdeal (𝓞 K)⁰ K)) ∧
      ∀ ξ ∈ (J : FractionalIdeal (𝓞 K)⁰ K), ξ ≠ 0 →
        κ₀ ≤ mixedEmbedding.norm (mixedEmbedding K ξ) := by
  obtain ⟨d, hd0, hd⟩ := exists_mul_mem_integralFiniteAdeles_of_isCompact hS
  set dK := algebraMap (𝓞 K) K d
  have hdK : dK ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr hd0
  have hNd : ((Algebra.norm ℚ dK : ℚ) : ℝ) ≠ 0 := by
    rw [Rat.cast_ne_zero]
    exact (Algebra.norm_ne_zero_iff).2 hdK
  refine ⟨Units.mk0 (FractionalIdeal.spanSingleton (𝓞 K)⁰ dK⁻¹)
    ((FractionalIdeal.spanSingleton_ne_zero_iff).mpr (inv_ne_zero hdK)),
    |((Algebra.norm ℚ dK : ℚ) : ℝ)|⁻¹, inv_pos.2 (abs_pos.2 hNd), ?_, ?_⟩
  · intro ξ hmem
    have h1 := hd _ hmem
    rw [← map_mul] at h1
    have h2 : dK * ξ ∈ ((1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) := by
      rw [← algebraMap_mem_idealFiniteAdeles_iff, ← SetLike.mem_coe, idealFiniteAdeles_one]
      exact h1
    rw [Units.val_one] at h2
    obtain ⟨r, hr⟩ := (FractionalIdeal.mem_one_iff _).mp h2
    refine (FractionalIdeal.mem_spanSingleton _).mpr ⟨r, ?_⟩
    rw [Algebra.smul_def, hr, mul_comm dK, mul_assoc, mul_inv_cancel₀ hdK, mul_one]
  · intro ξ hξ hξ0
    obtain ⟨r', hr'⟩ := (FractionalIdeal.mem_spanSingleton _).1 hξ
    have hr'0 : r' ≠ 0 := by
      rintro rfl
      rw [zero_smul] at hr'
      exact hξ0 hr'.symm
    have hmul : Algebra.norm ℚ dK * Algebra.norm ℚ ξ = Algebra.norm ℚ (r' : K) := by
      rw [← map_mul, ← hr', Algebra.smul_def, mul_left_comm, mul_inv_cancel₀ hdK, mul_one]
    have hξN : ((Algebra.norm ℚ ξ : ℚ) : ℝ) =
        ((Algebra.norm ℚ (r' : K) : ℚ) : ℝ) * ((Algebra.norm ℚ dK : ℚ) : ℝ)⁻¹ := by
      rw [← hmul, Rat.cast_mul]
      field_simp
    rw [mixedEmbedding.norm_eq_norm, Rat.cast_abs, hξN, abs_mul, abs_inv]
    exact le_mul_of_one_le_left (by positivity) (one_le_abs_norm_of_ne_zero hr'0)

theorem decay_real_bound {A B Z X₀ X₁ t κ : ℝ} {k n r : ℕ} (hA : 0 ≤ A) (hB : 0 < B) (hX₀ : 0 < X₀)
    (hX₁ : 0 < X₁) (ht : 0 < t) (hκ : 0 < κ) (h₀ : X₀ / B ≤ Z) (h₁ : X₁ / B ≤ Z)
    (h₂ : t * κ ≤ Z ^ n) :
    A * (Z ^ (k + k + n * r))⁻¹ ≤
      (t ^ r)⁻¹ * (A * B ^ (k + k) * (κ ^ r)⁻¹ * ((X₀ ^ k)⁻¹ * (X₁ ^ k)⁻¹)) := by
  have hY₀ : 0 < X₀ / B := div_pos hX₀ hB
  have hY₁ : 0 < X₁ / B := div_pos hX₁ hB
  have htκ : 0 < t * κ := mul_pos ht hκ
  have g₀ : (Z ^ k)⁻¹ ≤ ((X₀ / B) ^ k)⁻¹ := inv_anti₀ (pow_pos hY₀ k) (pow_le_pow_left₀ hY₀.le h₀ k)
  have g₁ : (Z ^ k)⁻¹ ≤ ((X₁ / B) ^ k)⁻¹ := inv_anti₀ (pow_pos hY₁ k) (pow_le_pow_left₀ hY₁.le h₁ k)
  have g₂ : ((Z ^ n) ^ r)⁻¹ ≤ ((t * κ) ^ r)⁻¹ :=
    inv_anti₀ (pow_pos htκ r) (pow_le_pow_left₀ htκ.le h₂ r)
  have hZ : 0 < Z := hY₀.trans_le h₀
  calc A * (Z ^ (k + k + n * r))⁻¹ = A * ((Z ^ k)⁻¹ * (Z ^ k)⁻¹ * ((Z ^ n) ^ r)⁻¹) := by
        rw [pow_add, pow_add, pow_mul, mul_inv, mul_inv]
    _ ≤ A * (((X₀ / B) ^ k)⁻¹ * ((X₁ / B) ^ k)⁻¹ * ((t * κ) ^ r)⁻¹) := by
        refine mul_le_mul_of_nonneg_left ?_ hA
        exact mul_le_mul (mul_le_mul g₀ g₁ (by positivity) (by positivity)) g₂ (by positivity)
          (by positivity)
    _ = (t ^ r)⁻¹ * (A * B ^ (k + k) * (κ ^ r)⁻¹ * ((X₀ ^ k)⁻¹ * (X₁ ^ k)⁻¹)) := by
        rw [div_pow, div_pow, inv_div, inv_div, mul_pow, mul_inv, pow_add]
        field_simp

theorem norm_le_norm_infC_moduleSection_mul (w : InfinitePlace K) {t : {x : ℝ // 0 < x}}
    (ht : 1 ≤ (t : ℝ)) (x : mixedSpace K) :
    ‖x‖ ≤ ‖infC ((moduleSection w t : IdeleGroup K) : 𝔸[K]) * x‖ := by
  set e := infC ((moduleSection w t : IdeleGroup K) : 𝔸[K])
  set e' := infC ((moduleSection w t⁻¹ : IdeleGroup K) : 𝔸[K])
  have hee : e' * e = 1 := by
    rw [← infC_mul, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
    simp only [infC, homeomorphMixedSpace_apply]
    exact map_one (InfiniteAdeleRing.ringEquiv_mixedSpace K)
  have he' : ∀ v, normAtPlace v e' ≤ 1 := by
    intro v
    simp only [e', infC]
    rw [normAtPlace_homeomorphMixedSpace]
    refine norm_moduleSection_apply_le_one w ?_ v
    change (t : ℝ)⁻¹ ≤ 1
    exact inv_le_one_of_one_le₀ ht
  calc ‖x‖ = ‖e' * (e * x)‖ := by rw [← mul_assoc, hee, one_mul]
    _ ≤ ‖e * x‖ := norm_mul_le_of_normAtPlace_le_one he' _

theorem norm_infC_moduleSection (w : InfinitePlace K) (t : {x : ℝ // 0 < x}) :
    mixedEmbedding.norm (infC ((moduleSection w t : IdeleGroup K) : 𝔸[K])) = t := by
  have h := mixedEmbedding_norm_toInfinite (moduleSection w t)
  rw [infiniteModule_moduleSection] at h
  exact h

end

end GlobalTheory.CompanionTheory.EisRk1
