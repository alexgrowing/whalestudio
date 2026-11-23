import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.CongrPIffInI
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.NormRepCountEqEulerFacInert
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsAddConjTransposeEq

open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.Cell

open LocalSpans idealPowerSpanBounds localizedQuotients WCA

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "κ" => algebraMap (𝓞 K) K

variable {𝔭 : Ideal (𝓞 F)}

theorem exists_of_normRepCount_ne_zero {Q : Ideal (𝓞 K)} {n : 𝓞 K} (h : normRepCount K Q 1 n ≠ 0) :
    ∃ α : 𝓞 K, conjO K α * α - n ∈ Q := by
  unfold normRepCount at h
  obtain ⟨⟨x, y, -, hy⟩⟩ := (Nat.card_ne_zero.mp h).1
  refine ⟨y 0, ?_⟩
  rw [Fin.sum_univ_one] at hy
  exact Ideal.Quotient.eq.mp hy

theorem exists_norm_congr (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (h𝔭 : 𝔭.IsMaximal) {c : 𝓞 F}
    (hc : c ∉ 𝔭) : ∃ α : 𝓞 K, ∃ ν : 𝓞 F, conjO K α * α = ι ν ∧ ν - c ∈ 𝔭 := by
  obtain ⟨P, hP, hPp⟩ := exists_maximal_over hK hF h𝔭
  have hcP : ι c ∉ P := fun h => hc (hPp ▸ Ideal.mem_comap.2 h)
  have hN := IdealNormInequalities.one_lt_absNorm hP
  have key : ∃ α : 𝓞 K, conjO K α * α - ι c ∈ P := by
    obtain ⟨h1, h2⟩ := localDensity K hK P hP 1 1 le_rfl le_rfl (ι c) (conjO_map hF c) hcP
    by_cases hc' : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P = P
    · have h3 := h1 hc'
      have hs : 0 < Real.sqrt (Ideal.absNorm P : ℝ) := Real.sqrt_pos.2 (by linarith)
      have hpos : (0 : ℝ) < (normRepCount K (P ^ 1) 1 (ι c) : ℝ) := by
        rw [h3]
        refine mul_pos (pow_pos hs _) ?_
        have : (0 : ℝ) < Real.sqrt (Ideal.absNorm P : ℝ) ^ (-((1 : ℕ) : ℤ)) := zpow_pos hs _
        linarith
      obtain ⟨α, hα⟩ := exists_of_normRepCount_ne_zero (by exact_mod_cast hpos.ne')
      exact ⟨α, by simpa using hα⟩
    · have h3 := h2 hc'
      have hpos : (0 : ℝ) < (normRepCount K ((P * Formalism.HermitianLatticesTheory.conjIdeal (K := K) P) ^ 1) 1 (ι c) : ℝ) := by
        rw [h3]
        refine mul_pos (pow_pos (by linarith) _) ?_
        have : (Ideal.absNorm P : ℝ) ^ (-((1 : ℕ) : ℤ)) < 1 := by
          rw [Nat.cast_one, zpow_neg_one]
          exact inv_lt_one_of_one_lt₀ hN
        linarith
      obtain ⟨α, hα⟩ := exists_of_normRepCount_ne_zero (by exact_mod_cast hpos.ne')
      rw [pow_one] at hα
      exact ⟨α, Ideal.mul_le_left hα⟩
  obtain ⟨α, hα⟩ := key
  obtain ⟨ν, hν⟩ := (conjO_eq_iff_mem_range hF (conjO K α * α)).1 (by
    rw [map_mul, conjO_conjO, mul_comm])
  refine ⟨α, ν, hν.symm, ?_⟩
  rw [← hPp, Ideal.mem_comap, map_sub, hν]
  exact hα

theorem exists_scale (hF : IsFixF K F) (h𝔭 : 𝔭.IsMaximal) {a₁ : 𝓞 F} {r k : ℕ}
    (h1 : a₁ ∈ 𝔭 ^ (r + r + k)) (h2 : a₁ ∉ 𝔭 ^ (r + r + k + 1)) :
    ∃ μ : K, μ ≠ 0 ∧ star μ = μ ∧ ∃ a : 𝓞 F, μ * μ * κ (ι a₁) = κ (ι a) ∧ a ∉ 𝔭 ^ (k + 1) := by
  have hp := h𝔭.isPrime
  have hp0 := ne_bot h𝔭
  obtain ⟨g, hg, hg'⟩ := Ideal.exists_mem_pow_notMem_pow_succ 𝔭 hp0 h𝔭.ne_top r
  have hgg : g * g ∉ 𝔭 ^ (r + r + 1) := mul_notMem hp hp0 hg' hg'
  have hgg0 : g * g ≠ 0 := fun h0 => hgg (h0 ▸ zero_mem _)
  have hg0 : g ≠ 0 := fun h0 => hgg0 (by rw [h0, zero_mul])
  have hκg := κι_ne_zero (K := K) hg0
  have hκgg := κι_ne_zero (K := K) hgg0
  set d := (κ (ι (g * g)))⁻¹ * κ (ι a₁) with hd
  have hd1 : InI 𝔭 k d := InI.div h𝔭 hgg0 hgg ((inI_ι h𝔭).2 h1)
  have hd2 : ¬ InI 𝔭 (k + 1) d := by
    intro hcon
    apply h2
    rw [← inI_ι (K := K) h𝔭]
    have e : κ (ι a₁) = κ (ι (g * g)) * d := by rw [hd]; field_simp
    rw [e, add_assoc]
    refine InI.mul hp ((inI_ι h𝔭).2 ?_) hcon
    rw [pow_add]
    exact Ideal.mul_mem_mul hg hg
  have hds : star d = d := by rw [hd, star_mul', star_inv₀, star_ι hF, star_ι hF]
  obtain ⟨t, δ, ht, e⟩ := exists_frac hF hds (hd1.mono (Nat.zero_le _))
  have hκt := κι_ne_zero (K := K) (ne_zero_of_notMem ht)
  refine ⟨κ (ι t) * (κ (ι g))⁻¹, mul_ne_zero hκt (inv_ne_zero hκg), ?_, t * δ, ?_, ?_⟩
  · rw [star_mul', star_inv₀, star_ι hF, star_ι hF]
  · rw [map_mul ι, map_mul κ, e, hd, map_mul ι g g, map_mul κ]
    field_simp
  · intro hcon
    apply hd2
    apply InI.of_mul hp ht
    apply InI.of_mul hp ht
    rw [← e, ← map_mul, ← map_mul]
    exact (inI_ι h𝔭).2 hcon

theorem exists_scale_int (hF : IsFixF K F) (h𝔭 : 𝔭.IsMaximal) {a₁ : 𝓞 F} (h0 : a₁ ≠ 0) :
    ∃ μ : K, μ ≠ 0 ∧ star μ = μ ∧ ∃ a : 𝓞 F, μ * μ * κ (ι a₁) = κ (ι a) ∧ a ∉ 𝔭 ^ 2 := by
  have h1 := localValuationFiltration.mem_pow_vF h𝔭 h0
  have h2 := localValuationFiltration.notMem_pow_vF h𝔭 h0
  have e : vF 𝔭 a₁ = vF 𝔭 a₁ / 2 + vF 𝔭 a₁ / 2 + vF 𝔭 a₁ % 2 := by omega
  rw [e] at h1 h2
  obtain ⟨μ, hμ0, hμs, a, ha, ha'⟩ := exists_scale (K := K) hF h𝔭 h1 h2
  exact ⟨μ, hμ0, hμs, a, ha, fun hm => ha' (Ideal.pow_le_pow_right (by omega) hm)⟩

theorem exists_scale_fixed (hF : IsFixF K F) (h𝔭 : 𝔭.IsMaximal) {d : K} (hd0 : d ≠ 0)
    (hds : star d = d) :
    ∃ μ : K, μ ≠ 0 ∧ star μ = μ ∧ ∃ a : 𝓞 F, μ * μ * d = κ (ι a) ∧ a ∉ 𝔭 ^ 2 := by
  obtain ⟨f, rfl⟩ := (hF d).1 hds
  obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 F) f
  have hy0 : y ≠ 0 := nonZeroDivisors.ne_zero hy
  have hκy := κι_ne_zero (K := K) hy0
  have e : algebraMap F K (algebraMap (𝓞 F) F x / algebraMap (𝓞 F) F y) = κ (ι x) / κ (ι y) := by
    rw [map_div₀]; rfl
  rw [e] at hd0 ⊢
  have hx0 : x ≠ 0 := by
    rintro rfl
    apply hd0
    simp
  obtain ⟨μ, hμ0, hμs, a, ha, ha'⟩ := exists_scale_int (K := K) hF h𝔭 (mul_ne_zero hy0 hx0)
  refine ⟨μ * κ (ι y), mul_ne_zero hμ0 hκy, by rw [star_mul', hμs, star_ι hF], a, ?_, ha'⟩
  rw [← ha, map_mul ι, map_mul κ]
  field_simp

theorem exists_alpha (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (h𝔭 : 𝔭.IsMaximal) {a a' : 𝓞 F}
    (ha : a ∈ 𝔭) (ha2 : a ∉ 𝔭 ^ 2) (ha' : a' ∈ 𝔭) (ha'2 : a' ∉ 𝔭 ^ 2) :
    ∃ α : 𝓞 K, ∃ ν : 𝓞 F, conjO K α * α = ι ν ∧ a * ν + a' ∈ 𝔭 ^ 2 ∧ a * ν + a' ∉ 𝔭 ^ 3 := by
  have hp := h𝔭.isPrime
  have hp0 := ne_bot h𝔭
  have h1 : -a' ∈ Ideal.span {a} ⊔ 𝔭 ^ 2 :=
    pow_le_span_sup hp hp0 (c := 1) (by simpa using ha2) 2 (by simpa using ha')
  obtain ⟨c, r, hr, e⟩ := Ideal.mem_span_singleton_sup.1 h1
  have hc : c ∉ 𝔭 := by
    intro hc
    apply ha'2
    have : a' = -(c * a + r) := by rw [e]; ring
    rw [this]
    refine neg_mem (add_mem ?_ hr)
    rw [pow_two]
    exact Ideal.mul_mem_mul hc ha
  obtain ⟨α₀, ν₀, hν₀, hνc⟩ := exists_norm_congr hK hF h𝔭 hc
  have hν₀p : ν₀ ∉ 𝔭 := fun h => hc (by simpa using sub_mem h hνc)
  have h2 : a * ν₀ + a' ∈ 𝔭 ^ 2 := by
    have : a * ν₀ + a' = a * (ν₀ - c) - r := by linear_combination e
    rw [this]
    refine sub_mem ?_ hr
    rw [pow_two]
    exact Ideal.mul_mem_mul ha hνc
  by_cases h3 : a * ν₀ + a' ∈ 𝔭 ^ 3
  · obtain ⟨τ, hτ⟩ := exists_add_conj_eq hK hF (1 : 𝓞 F)
    obtain ⟨t₂, ht₂⟩ := (conjO_eq_iff_mem_range hF (conjO K τ * τ)).1 (by
      rw [map_mul, conjO_conjO, mul_comm])
    refine ⟨α₀ * (1 + ι a * τ), ν₀ * (1 + a + a * a * t₂), ?_, ?_, ?_⟩
    · rw [map_mul, map_add, map_mul, map_one, conjO_map hF, map_mul ι, map_add ι, map_add ι, map_mul ι,
        map_mul ι, map_one, ← hν₀, ht₂]
      rw [map_one] at hτ
      linear_combination (conjO K α₀ * α₀ * ι a) * hτ
    · have : a * (ν₀ * (1 + a + a * a * t₂)) + a' =
          (a * ν₀ + a') + a * a * (ν₀ * (1 + a * t₂)) := by ring
      rw [this]
      refine add_mem h2 (Ideal.mul_mem_right _ _ ?_)
      rw [pow_two]
      exact Ideal.mul_mem_mul ha ha
    · intro hcon
      have h4 : a * a * a * (ν₀ * t₂) ∈ 𝔭 ^ 3 := by
        refine Ideal.mul_mem_right _ _ ?_
        rw [pow_succ, pow_two]
        exact Ideal.mul_mem_mul (Ideal.mul_mem_mul ha ha) ha
      have ha2' : a ∉ 𝔭 ^ (1 + 1) := by simpa using ha2
      have hν' : ν₀ ∉ 𝔭 ^ (0 + 1) := by simpa using hν₀p
      have h5 : a * a * ν₀ ∉ 𝔭 ^ 3 := by
        have := mul_notMem hp hp0 (mul_notMem hp hp0 ha2' ha2') hν'
        simpa using this
      apply h5
      have : a * a * ν₀ = (a * (ν₀ * (1 + a + a * a * t₂)) + a') - (a * ν₀ + a') -
          a * a * a * (ν₀ * t₂) := by ring
      rw [this]
      exact sub_mem (sub_mem hcon h3) h4
  · exact ⟨α₀, ν₀, hν₀, h2, h3⟩

end Formalism.HermitianLattices.Ext.L3.Cell
