import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.SpanPowMulLe

open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.HU

open LocalSpans idealPowerSpanBounds localizedQuotients

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "jK" => algebraMap (𝓞 K) K

structure IsUnif0 (𝔭 : Ideal (𝓞 F)) (π₀ s₀ : 𝓞 F) : Prop where
  mem : π₀ ∈ 𝔭
  notMem : π₀ ∉ 𝔭 ^ 2
  s_notMem : s₀ ∉ 𝔭
  le : Ideal.span {s₀} * 𝔭 ≤ Ideal.span {π₀}

theorem exists_isUnif0 {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) : ∃ π₀ s₀, IsUnif0 𝔭 π₀ s₀ := by
  obtain ⟨π₀, h1, h2, s₀, h3, h4⟩ := exists_unif0 h𝔭
  exact ⟨π₀, s₀, ⟨h1, h2, h3, h4⟩⟩

theorem jι_ne_zero {a : 𝓞 F} (ha : a ≠ 0) : jK (ι a) ≠ 0 := by
  intro h0
  apply ha
  have h1 : algebraMap F K (a : F) = 0 := h0
  rw [map_eq_zero] at h1
  first
  | exact_mod_cast h1
  | exact RingOfIntegers.ext h1

theorem IsUnif0.ne_zero {𝔭 : Ideal (𝓞 F)} {π₀ s₀ : 𝓞 F} (hu : IsUnif0 𝔭 π₀ s₀) : π₀ ≠ 0 := by
  rintro rfl
  exact hu.notMem (Submodule.zero_mem _)

theorem ne_zero_of_notMem {𝔭 : Ideal (𝓞 F)} {t : 𝓞 F} (ht : t ∉ 𝔭) : t ≠ 0 := by
  rintro rfl
  exact ht (Submodule.zero_mem _)

theorem mem_noncompactPart_iff {𝔭 : Ideal (𝓞 F)} [h𝔭 : 𝔭.IsPrime] {π₀ s₀ : 𝓞 F} (hu : IsUnif0 𝔭 π₀ s₀) (k : ℕ)
    (a : K) : InP 𝔭 k a ↔ ∃ s ∈ SP K 𝔭, a = jK (ι π₀) ^ k * s := by
  have hp : 𝔭.IsPrime := h𝔭
  constructor
  · rintro ⟨t, ht, z, hz, e⟩
    have hmem : ι (s₀ ^ k) * z ∈ Ideal.span {ι (π₀ ^ k)} :=
      span_pow_mul_le hu.le k (Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) hz)
    obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.mp hmem
    have htu : t * s₀ ^ k ∉ 𝔭 := fun hm =>
      (hp.mem_or_mem hm).elim ht (fun h => hu.s_notMem (hp.mem_of_pow_mem k h))
    have hd : jK (ι (t * s₀ ^ k)) ≠ 0 := jι_ne_zero (ne_zero_of_notMem htu)
    refine ⟨jK w / jK (ι (t * s₀ ^ k)), mem_SP.mpr ⟨t * s₀ ^ k, htu, w, ?_⟩, ?_⟩
    · rw [mul_div_assoc', eq_div_iff hd, mul_comm]
    · have hw' := congrArg jK hw
      simp only [map_mul, map_pow] at hw'
      rw [mul_div_assoc', eq_div_iff hd]
      simp only [map_mul, map_pow]
      linear_combination -hw' - jK (ι s₀) ^ k * e
  · rintro ⟨s, hs, rfl⟩
    have h1 : InP 𝔭 k (jK (ι π₀) ^ k) := by
      rw [← map_pow]
      exact inP_jK (Ideal.pow_mem_pow (Ideal.mem_map_of_mem _ hu.mem) k)
    have h2 := h1.mul (show InP 𝔭 0 s from hs)
    simpa using h2

theorem exists_norm (hF : IsFixF K F) (u : 𝓞 K) : ∃ n₀ : 𝓞 F, ι n₀ = u * conjO K u := by
  have hs : star (jK (u * conjO K u)) = jK (u * conjO K u) := by
    rw [map_mul]
    show star (jK u * star (jK u)) = jK u * star (jK u)
    rw [star_mul, star_star, mul_comm]
  obtain ⟨f, hf⟩ := (hF _).mp hs
  have hint : IsIntegral ℤ f := by
    have h1 : IsIntegral ℤ (algebraMap F K f) := by
      rw [hf]
      exact (u * conjO K u).isIntegral_coe
    exact (isIntegral_algHom_iff ((algebraMap F K).toIntAlgHom) (algebraMap F K).injective).mp h1
  exact ⟨⟨f, hint⟩, RingOfIntegers.ext hf⟩

theorem isLocUnif (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) [hp : 𝔭.IsPrime] {π₀ s₀ : 𝓞 F} (hu : IsUnif0 𝔭 π₀ s₀) :
    IsLocUnif (SP K 𝔭) (jK (ι π₀)) where
  star_mem := fun a ha => InP.conj hF ha
  mem := jK_mem_SP _
  fix := star_ι hF _
  ne := jι_ne_zero hu.ne_zero
  tr := by
    obtain ⟨z, hz⟩ := exists_add_conj_eq hK hF (1 : 𝓞 F)
    refine ⟨jK z, jK_mem_SP _, ?_⟩
    have := congrArg jK hz
    rw [map_add, map_one, map_one] at this
    exact this
  skew := by
    obtain ⟨P, hP, -⟩ := exists_maximal_over hK hF h𝔭
    obtain ⟨θ, hθ⟩ := exists_sub_conjO_notMem hK hP
    refine ⟨jK (θ - conjO K θ), jK_mem_SP _, ?_, ?_⟩
    · have : star (jK (θ - conjO K θ)) = jK (conjO K (θ - conjO K θ)) := rfl
      rw [this, map_sub, L3.conjO_conjO, ← map_neg]
      congr 1
      ring
    · intro h
      apply hθ
      rw [jK_inj (h.trans (map_zero _).symm)]
      exact zero_mem _
  dv := by
    intro f hf hfix
    obtain ⟨t, ht, z, e⟩ := mem_SP.1 hf
    have hzfix : conjO K z = z := by
      apply jK_inj
      have : jK (conjO K z) = star (jK z) := rfl
      rw [this, e, star_mul', star_ι hF, hfix]
    obtain ⟨z₀, rfl⟩ := (conjO_eq_iff_mem_range hF z).1 hzfix
    have ht0 : jK (ι t) ≠ 0 := jι_ne_zero (ne_zero_of_notMem ht)
    by_cases hz : z₀ ∈ 𝔭
    · right
      have h1 := hu.le (Ideal.mul_mem_mul (Ideal.mem_span_singleton_self s₀) hz)
      obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 h1
      refine mem_SP.2 ⟨t * s₀, fun h => (hp.mem_or_mem h).elim ht hu.s_notMem, ι y, ?_⟩
      have hϖ : jK (ι π₀) ≠ 0 := jι_ne_zero hu.ne_zero
      have h2 := congrArg (fun x => jK (ι x)) hy
      simp only [map_mul] at h2 ⊢
      field_simp
      rw [h2, e]
      ring
    · left
      have hz0 : jK (ι z₀) ≠ 0 := jι_ne_zero (ne_zero_of_notMem hz)
      have hf0 : f ≠ 0 := by
        rintro rfl
        rw [mul_zero] at e
        exact hz0 e
      refine mem_SP.2 ⟨z₀, hz, ι t, ?_⟩
      rw [e]
      field_simp
  rad := by
    intro s hs
    obtain ⟨t, ht, z, e⟩ := mem_SP.1 hs
    have ht0 : jK (ι t) ≠ 0 := jι_ne_zero (ne_zero_of_notMem ht)
    obtain ⟨n₀, hn₀⟩ := exists_norm hF (ι t + ι π₀ * z)
    have hn : n₀ ∉ 𝔭 := by
      intro hmem
      have h1 : ι (n₀ - t * t) ∈ extP K 𝔭 ^ 1 := by
        have : ι (n₀ - t * t) = ι π₀ * (z * ι t + ι t * conjO K z + ι π₀ * z * conjO K z) := by
          rw [map_sub, hn₀, map_add, map_mul (conjO K), conjO_map hF, conjO_map hF, map_mul]
          ring
        rw [this]
        exact Ideal.mul_mem_right _ _ (ι_mem_pow (by rw [pow_one]; exact hu.mem))
      rw [mem_pow_iff, pow_one] at h1
      have h2 : t * t ∈ 𝔭 := by
        have := sub_mem hmem h1
        rwa [sub_sub_cancel] at this
      exact (hp.mem_or_mem h2).elim ht ht
    have hn0 : jK (ι n₀) ≠ 0 := jι_ne_zero (ne_zero_of_notMem hn)
    have e1 : jK (ι t) * (1 + jK (ι π₀) * s) = jK (ι t + ι π₀ * z) := by
      rw [map_add, map_mul, e]
      ring
    have e2 : jK (ι n₀) = jK (ι t + ι π₀ * z) * jK (conjO K (ι t + ι π₀ * z)) := by
      rw [hn₀, map_mul]
    have hne : 1 + jK (ι π₀) * s ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at e1
      rw [← e1, zero_mul] at e2
      exact hn0 e2
    refine ⟨hne, mem_SP.2 ⟨n₀, hn, ι t * conjO K (ι t + ι π₀ * z), ?_⟩⟩
    rw [e2, ← e1, map_mul]
    field_simp
  arch := by
    intro a
    obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) a
    have hy0 : y ≠ 0 := nonZeroDivisors.ne_zero hy
    obtain ⟨n₀, hn₀⟩ := exists_norm hF y
    have hcy : conjO K y ≠ 0 := by
      intro h
      apply hy0
      rw [← L3.conjO_conjO y, h, map_zero]
    have hn0 : n₀ ≠ 0 := by
      rintro rfl
      rw [map_zero] at hn₀
      exact (mul_ne_zero hy0 hcy) hn₀.symm
    have hc' : Ideal.span {n₀} ≠ (0 : Ideal (𝓞 F)) := by simpa using hn0
    have hnu : ¬ IsUnit 𝔭 := by
      rw [Ideal.isUnit_iff]
      exact h𝔭.ne_top
    obtain ⟨𝔟, hb, hnd⟩ := (FiniteMultiplicity.of_not_isUnit hnu hc').exists_eq_pow_mul_and_not_dvd
    rw [Ideal.dvd_iff_le] at hnd
    obtain ⟨t, ht, ht'⟩ := SetLike.not_le_iff_exists.1 hnd
    generalize multiplicity 𝔭 (Ideal.span {n₀}) = l at hb
    refine ⟨l, mem_SP.2 ⟨t, ht', ?_⟩⟩
    have h1 : π₀ ^ l * t ∈ Ideal.span {n₀} := by
      rw [hb]
      exact Ideal.mul_mem_mul (Ideal.pow_mem_pow hu.mem _) ht
    obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.1 h1
    refine ⟨ι w * conjO K y * x, ?_⟩
    have hyK : jK y ≠ 0 := fun h => hy0 (jK_inj (h.trans (map_zero _).symm))
    have h2 := congrArg (fun x => jK (ι x)) hw
    simp only [map_mul, map_pow, hn₀] at h2 ⊢
    field_simp
    linear_combination (jK x) * h2

end Formalism.HermitianLattices.Ext.L3.HU
