import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.SameGenusFix
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.SpanPowMulLe
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsLocalData
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.MemSmulOfMemSmulLocF
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.FiniteDimensionalOfOrtho

open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.G2

open Formalism.HermitianLattices.Ext.L3

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "jK" => algebraMap (𝓞 K) K

theorem jK_ι (t : 𝓞 F) : jK (ι t) = algebraMap F K (t : F) := rfl

theorem jK_ι_ne_zero {t : 𝓞 F} (ht : t ≠ 0) : jK (ι t) ≠ 0 := by
  rw [jK_ι]
  intro h
  apply ht
  have h1 : ((t : F)) = 0 := (map_eq_zero_iff _ (algebraMap F K).injective).1 h
  exact_mod_cast h1

theorem ne_zero_of_notMem {𝔭 : Ideal (𝓞 F)} {t : 𝓞 F} (ht : t ∉ 𝔭) : t ≠ 0 := by
  rintro rfl
  exact ht 𝔭.zero_mem

theorem exists_inv_mod {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {t : 𝓞 F} (ht : t ∉ 𝔭) (e : ℕ) :
    ∃ u : 𝓞 F, 1 - t * u ∈ 𝔭 ^ e := by
  obtain ⟨y, i, hi, hyi⟩ := h𝔭.exists_inv ht
  refine ⟨y * ∑ k ∈ Finset.range e, i ^ k, ?_⟩
  have h1 : t * (y * ∑ k ∈ Finset.range e, i ^ k) = 1 - i ^ e := by
    rw [← mul_neg_geom_sum, ← hyi]
    ring
  rw [h1, sub_sub_cancel]
  exact Ideal.pow_mem_pow hi e

theorem exists_mul_mem_span {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {a : 𝓞 F} (ha : a ≠ 0) :
    ∃ t : 𝓞 F, t ∉ 𝔭 ∧ ∀ x ∈ 𝔭 ^ vF 𝔭 a, t * x ∈ Ideal.span {a} := by
  have hle : Ideal.span {a} ≤ 𝔭 ^ vF 𝔭 a :=
    (Ideal.span_singleton_le_iff_mem _).2 (localValuationFiltration.mem_pow_vF h𝔭 ha)
  obtain ⟨J, hJ⟩ := Ideal.dvd_iff_le.2 hle
  have hJp : ¬ J ≤ 𝔭 := by
    intro hJ𝔭
    apply localValuationFiltration.notMem_pow_vF h𝔭 ha
    have : Ideal.span {a} ≤ 𝔭 ^ (vF 𝔭 a + 1) := by
      rw [hJ, pow_succ]
      exact Ideal.mul_mono_right hJ𝔭
    exact this (Ideal.mem_span_singleton_self a)
  obtain ⟨t, htJ, ht𝔭⟩ := SetLike.not_le_iff_exists.1 hJp
  refine ⟨t, ht𝔭, fun x hx => ?_⟩
  rw [hJ, mul_comm t x]
  exact Ideal.mul_mem_mul hx htJ

theorem div_mem_SP_iff {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {a : 𝓞 F} (ha : a ≠ 0) (z : 𝓞 K) :
    haveI := h𝔭.isPrime
    jK z / jK (ι a) ∈ HU.SP K 𝔭 ↔ z ∈ extP K 𝔭 ^ vF 𝔭 a := by
  have := h𝔭.isPrime
  have ha' := jK_ι_ne_zero (K := K) ha
  rw [HU.mem_SP]
  constructor
  · rintro ⟨t, ht, w, hw⟩
    have e1 : ι t * z = w * ι a := by
      apply FaithfulSMul.algebraMap_injective (𝓞 K) K
      rw [map_mul, map_mul, hw]
      field_simp
    obtain ⟨u, hu⟩ := exists_inv_mod h𝔭 ht (vF 𝔭 a)
    have hA : ι a ∈ extP K 𝔭 ^ vF 𝔭 a := localizedQuotients.ι_mem_pow (localValuationFiltration.mem_pow_vF h𝔭 ha)
    have e2 : z = ι u * (ι t * z) + ι (1 - t * u) * z := by
      rw [map_sub, map_mul, map_one]
      ring
    rw [e2, e1]
    exact Submodule.add_mem _ (Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ hA))
      (Ideal.mul_mem_right _ _ (localizedQuotients.ι_mem_pow hu))
  · intro hz
    obtain ⟨t, ht, htx⟩ := exists_mul_mem_span h𝔭 ha
    refine ⟨t, ht, ?_⟩
    have hle : Ideal.span {ι t} * extP K 𝔭 ^ vF 𝔭 a ≤ Ideal.span {ι a} := by
      rw [Ideal.span_singleton_mul_le_iff]
      intro y hy
      unfold extP at hy
      rw [← Ideal.map_pow] at hy
      refine Submodule.span_induction (p := fun y _ => ι t * y ∈ Ideal.span {ι a}) ?_ ?_ ?_ ?_ hy
      · rintro _ ⟨x, hx, rfl⟩
        obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (htx x hx)
        rw [← map_mul, ← hc, map_mul]
        exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
      · simp
      · intro x y _ _ hx hy
        rw [mul_add]
        exact Submodule.add_mem _ hx hy
      · intro c x _ hx
        rw [smul_eq_mul, mul_left_comm]
        exact Ideal.mul_mem_left _ _ hx
    obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.1
      (hle (Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) hz))
    refine ⟨w, ?_⟩
    have := congrArg jK hw
    rw [map_mul, map_mul] at this
    field_simp
    rw [this]

theorem exists_sub_div_mem_SP {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {a : 𝓞 F} (ha : a ≠ 0) {r : K}
    (hr : haveI := h𝔭.isPrime; r ∈ HU.SP K 𝔭) :
    haveI := h𝔭.isPrime
    ∃ z : 𝓞 K, (r - jK z) / jK (ι a) ∈ HU.SP K 𝔭 := by
  have := h𝔭.isPrime
  obtain ⟨t, ht, w, hw⟩ := HU.mem_SP.1 hr
  obtain ⟨u, hu⟩ := exists_inv_mod h𝔭 ht (vF 𝔭 a)
  refine ⟨ι u * w, ?_⟩
  have h1 : jK (ι (1 - t * u)) / jK (ι a) ∈ HU.SP K 𝔭 :=
    (div_mem_SP_iff h𝔭 ha _).2 (localizedQuotients.ι_mem_pow hu)
  have e : (r - jK (ι u * w)) / jK (ι a) = r * (jK (ι (1 - t * u)) / jK (ι a)) := by
    rw [map_mul, hw, map_sub, map_mul, map_one, map_sub, map_mul, map_one]
    ring
  rw [e]
  exact Subring.mul_mem _ hr h1

theorem star_jK (w : 𝓞 K) : ∃ w' : 𝓞 K, jK w' = star (jK w) := StandardSymmetricSums.star_int w

theorem star_jK_ι (hF : IsFixF K F) (t : 𝓞 F) : star (jK (ι t)) = jK (ι t) :=
  (hF _).2 ⟨(t : F), rfl⟩

theorem exists_common {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {ι' : Type} (s : Finset ι') (r : ι' → K)
    (hr : haveI := h𝔭.isPrime; ∀ i ∈ s, r i ∈ HU.SP K 𝔭) :
    ∃ t : 𝓞 F, t ∉ 𝔭 ∧ ∀ i ∈ s, ∃ w : 𝓞 K, jK w = jK (ι t) * r i := by
  classical
  have := h𝔭.isPrime
  induction s using Finset.induction_on with
  | empty => exact ⟨1, fun h => h𝔭.ne_top ((Ideal.eq_top_iff_one _).2 h), by simp⟩
  | insert j s hj ih =>
    obtain ⟨t, ht, hts⟩ := ih (fun i hi => hr i (Finset.mem_insert_of_mem hi))
    obtain ⟨t', ht', w', hw'⟩ := HU.mem_SP.1 (hr j (Finset.mem_insert_self j s))
    refine ⟨t * t', fun hm => (h𝔭.isPrime.mem_or_mem hm).elim ht ht', fun i hi => ?_⟩
    rcases Finset.mem_insert.1 hi with rfl | hi
    · refine ⟨ι t * w', ?_⟩
      rw [map_mul, hw', map_mul, map_mul]
      ring
    · obtain ⟨w, hw⟩ := hts i hi
      refine ⟨ι t' * w, ?_⟩
      rw [map_mul, hw, map_mul, map_mul]
      ring

end Formalism.L2.SG.Pf.G2
