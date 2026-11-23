import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeDEqSumOfAgree
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

noncomputable section

namespace GlobalTheory.IsoInteg

open ValuativeRel Filter Topology

section Val

variable {K K' : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field K'] [ValuativeRel K'] [TopologicalSpace K'] [IsNonarchimedeanLocalField K']

theorem tendsto_pow_zero_of_lt_one {x : K} (h : valuation K x < 1) :
    Tendsto (fun n : ℕ => x ^ n) atTop (𝓝 0) := by
  rw [(IsValuativeTopology.hasBasis_nhds_zero' K).tendsto_right_iff]
  intro γ hγ
  have : MulArchimedean (ValueGroupWithZero K) :=
    ValuativeRel.isRankLeOne_iff_mulArchimedean.mp inferInstance
  obtain ⟨n, hn⟩ := exists_pow_lt₀ h (Units.mk0 γ hγ)
  filter_upwards [eventually_ge_atTop n] with m hm
  rw [map_pow]
  exact lt_of_le_of_lt (pow_le_pow_right_of_le_one' h.le hm) hn

theorem lt_one_of_continuous (i : K →+* K') (hi : Continuous i) {x : K} (h : valuation K x < 1) :
    valuation K' (i x) < 1 := by
  have h1 : Tendsto (fun n : ℕ => i x ^ n) atTop (𝓝 0) := by
    have := (hi.tendsto 0).comp (tendsto_pow_zero_of_lt_one h)
    simpa [Function.comp_def, map_pow] using this
  have hU : {y : K' | valuation K' y < 1} ∈ 𝓝 (0 : K') :=
    (IsValuativeTopology.hasBasis_nhds_zero' K').mem_iff.2 ⟨1, one_ne_zero, fun y hy => hy⟩
  obtain ⟨N, hN⟩ := (h1.eventually hU).exists
  by_contra hc
  push_neg at hc
  have : 1 ≤ valuation K' (i x ^ N) := by rw [map_pow]; exact one_le_pow₀ hc
  exact absurd hN (not_lt.2 this)

theorem le_one_of_map_le_one (i : K →+* K') (hi : Continuous i) {y : K} (h : valuation K' (i y) ≤ 1) :
    valuation K y ≤ 1 := by
  by_contra hc
  push_neg at hc
  have hy : y ≠ 0 := fun h0 => by simp [h0] at hc
  have h1 : valuation K y⁻¹ < 1 := by rw [map_inv₀]; exact inv_lt_one_of_one_lt₀ hc
  have h2 := lt_one_of_continuous i hi h1
  rw [map_inv₀, map_inv₀] at h2
  have h0 : (0 : ValueGroupWithZero K') < valuation K' (i y) := by
    rw [zero_lt_iff, Valuation.ne_zero_iff]
    exact (map_ne_zero i).2 hy
  exact absurd h (not_le.2 ((inv_lt_one₀ h0).1 h2))

theorem map_le_one (i : K →+* K') (hi : Continuous i) {y : K} (h : valuation K y ≤ 1) :
    valuation K' (i y) ≤ 1 := by
  by_contra hc
  push_neg at hc
  have hy : y ≠ 0 := fun h0 => by simp [h0] at hc
  obtain ⟨x, hx0, hx1⟩ := Valuation.IsNontrivial.exists_lt_one (v := valuation K)
  have hx : x ≠ 0 := fun h0 => hx0 (by simp [h0])
  have hγ : valuation K' (i x) ≠ 0 := by
    rw [Valuation.ne_zero_iff]; exact (map_ne_zero i).2 hx
  have hpos : (0 : ValueGroupWithZero K') < valuation K' (i y) := zero_lt_one.trans hc
  have hinv : valuation K' (i y)⁻¹ < 1 := by rw [map_inv₀]; exact inv_lt_one_of_one_lt₀ hc
  have ht := tendsto_pow_zero_of_lt_one hinv
  rw [(IsValuativeTopology.hasBasis_nhds_zero' K').tendsto_right_iff] at ht
  obtain ⟨n, hn⟩ := (ht _ hγ).exists
  have hxy : valuation K (x * y ^ n) < 1 := by
    rw [map_mul, map_pow]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' (pow_le_one' h n)) hx1
  have h2 := lt_one_of_continuous i hi hxy
  rw [map_mul, map_pow, map_mul, map_pow] at h2
  simp only [Set.mem_setOf_eq, map_pow, map_inv₀] at hn
  have hpn : (0 : ValueGroupWithZero K') < valuation K' (i y) ^ n := pow_pos hpos n
  rw [inv_pow] at hn
  have := (inv_lt_iff_one_lt_mul₀ hpn).1 hn
  exact absurd h2 (not_lt.2 this.le)

end Val

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem valued_le_one_iff_of_continuous : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E)) (i : v.adicCompletion F ≃+* w.adicCompletion E),
    Continuous i → ∀ a : v.adicCompletion F, Valued.v (i a) ≤ 1 ↔ Valued.v a ≤ 1 := by
  intro F E _ _ _ _ v w i hi a
  rw [← GlobalTheory.CuspRep.ParLaws.valuation_le_one_iff w, ← GlobalTheory.CuspRep.ParLaws.valuation_le_one_iff v]
  exact ⟨le_one_of_map_le_one i.toRingHom hi, map_le_one i.toRingHom hi⟩

end GlobalTheory.IsoInteg

end
