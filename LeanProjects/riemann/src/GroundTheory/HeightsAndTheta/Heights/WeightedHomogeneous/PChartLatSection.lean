import Mathlib
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ReciprocityTheory.ChartRestriction.G

noncomputable section

namespace ChartLatSection

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ} {Ω : Type} [Field Ω]

theorem mConeMap_form (y : Coord n → Ω) {f : MvPolynomial (Coord n) ℤ} {δ : ι → ℕ}
    (hf : IsWeightedHomogeneous (coordDeg n) f δ) :
    Geo.mConeMap (ι := blockIdx n) y f = C (aeval y f) * ∏ k, (X k : MvPolynomial ι Ω) ^ δ k := by
  have hg := (geoMultiHomog_iff f δ).mpr hf
  conv_lhs => rw [f.as_sum]
  conv_rhs => rw [f.as_sum]
  rw [map_sum, map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hdeg := hg m hm
  simp only [Geo.mConeMap, aeval_monomial, map_mul]
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp only [mul_pow, Finset.prod_mul_distrib, map_prod, map_pow]
  have hX : (∏ p : Coord n, (X p.1 : MvPolynomial ι Ω) ^ m p) = ∏ k, (X k : MvPolynomial ι Ω) ^ δ k := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    show ∏ i, (X k : MvPolynomial ι Ω) ^ m ⟨k, i⟩ = _
    rw [Finset.prod_pow_eq_pow_sum, hdeg k]
  rw [hX, MvPolynomial.algebraMap_apply]
  ring

theorem form_mem_iff (y : Coord n → Ω) {f : MvPolynomial (Coord n) ℤ} {δ : ι → ℕ}
    (hf : IsWeightedHomogeneous (coordDeg n) f δ) :
    f ∈ Geo.mCoordIdeal (ι := blockIdx n) y ↔ aeval y f = 0 := by
  rw [Geo.mCoordIdeal, RingHom.mem_ker, mConeMap_form y hf]
  constructor
  · intro h
    have hM : (∏ k, (X k : MvPolynomial ι Ω) ^ δ k) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (X_ne_zero k)
    exact C_eq_zero.mp ((mul_eq_zero.mp h).resolve_right hM)
  · intro h
    rw [h, C_0, zero_mul]

omit [Fintype ι] [DecidableEq ι] in

theorem aeval_eq_zero_of_mem (y : Coord n → Ω) {f : MvPolynomial (Coord n) ℤ}
    (hf : f ∈ Geo.mCoordIdeal (ι := blockIdx n) y) : aeval y f = 0 := by
  have h1 : (aeval (fun _ : ι => (1 : Ω))).toRingHom.comp
      (Geo.mConeMap (ι := blockIdx n) y).toRingHom = (aeval y : _ →ₐ[ℤ] Ω).toRingHom := by
    refine MvPolynomial.ringHom_ext (fun r => by simp) (fun v => by simp [Geo.mConeMap])
  have h2 := congrArg (fun φ : _ →+* _ => φ f) h1
  have h3 : Geo.mConeMap (ι := blockIdx n) y f = 0 := RingHom.mem_ker.mp hf
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, h3, map_zero] at h2
  rw [← h2]

omit [DecidableEq ι] in

theorem aeval_chartMonomial (y : Coord n → Ω) (c : (k : ι) → Fin (n k + 1)) (d : ι → ℕ) :
    aeval y (chartMonomial c d) = ∏ k, y ⟨k, c k⟩ ^ d k := by
  simp [chartMonomial, map_prod]

theorem coord_notMem_iff (y : Coord n → Ω) {P : ArithVariety n}
    (hP : P.ideal = Geo.mCoordIdeal (ι := blockIdx n) y) (p : Coord n) :
    (X p : MvPolynomial (Coord n) ℤ) ∉ P.ideal ↔ y p ≠ 0 := by
  rw [hP, form_mem_iff y (isWeightedHomogeneous_X ℤ (coordDeg n) p), aeval_X]

theorem exists_form_of_mem_chartRingZ (y : Coord n → Ω) (c : (k : ι) → Fin (n k + 1))
    (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) {x : Ω} (hx : x ∈ Geo.chartRingZ (ι := blockIdx n) y c) :
    ∃ (δ : ι → ℕ) (e : MvPolynomial (Coord n) ℤ), IsWeightedHomogeneous (coordDeg n) e δ ∧
      aeval y e = x * ∏ k, y ⟨k, c k⟩ ^ δ k := by
  have hpow : ∀ δ₁ δ₂ : ι → ℕ, ∏ k, y ⟨k, c k⟩ ^ (δ₁ + δ₂) k =
      (∏ k, y ⟨k, c k⟩ ^ δ₁ k) * ∏ k, y ⟨k, c k⟩ ^ δ₂ k := fun δ₁ δ₂ => by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun k _ => by rw [Pi.add_apply, pow_add]
  rw [Geo.chartRingZ] at hx
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨p, rfl⟩ := hx
    refine ⟨coordDeg n p, X p, isWeightedHomogeneous_X ℤ _ p, ?_⟩
    have h1 : ∏ k, y ⟨k, c k⟩ ^ coordDeg n p k = y ⟨p.1, c p.1⟩ := by
      rw [Finset.prod_eq_single p.1 (fun k _ hk => by simp [coordDeg, hk])
        (fun h => absurd (Finset.mem_univ _) h)]
      simp [coordDeg]
    rw [aeval_X, h1, div_mul_cancel₀ _ (hc p.1)]
  | algebraMap r =>
    exact ⟨0, C r, isWeightedHomogeneous_C _ _, by simp⟩
  | add x z _ _ hx hz =>
    obtain ⟨δ₁, e₁, h₁, v₁⟩ := hx
    obtain ⟨δ₂, e₂, h₂, v₂⟩ := hz
    refine ⟨δ₁ + δ₂, e₁ * chartMonomial c δ₂ + e₂ * chartMonomial c δ₁,
      (h₁.mul (isWeightedHomogeneous_chartMonomial c δ₂)).add ?_, ?_⟩
    · rw [add_comm δ₁]
      exact h₂.mul (isWeightedHomogeneous_chartMonomial c δ₁)
    · rw [map_add, map_mul, map_mul, v₁, v₂, aeval_chartMonomial, aeval_chartMonomial, hpow]
      ring
  | mul x z _ _ hx hz =>
    obtain ⟨δ₁, e₁, h₁, v₁⟩ := hx
    obtain ⟨δ₂, e₂, h₂, v₂⟩ := hz
    refine ⟨δ₁ + δ₂, e₁ * e₂, h₁.mul h₂, ?_⟩
    rw [map_mul, v₁, v₂, hpow]
    ring

theorem exists_chartForm (y : Coord n → Ω) (a : ι → ℤ) (τ : ℕ) {s : Ω}
    (hs : s ∈ Geo.chartLat (ι := blockIdx n) y a τ) (c : (k : ι) → Fin (n k + 1))
    (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) :
    ∃ (d δ : ι → ℕ) (e : MvPolynomial (Coord n) ℤ), IsWeightedHomogeneous (coordDeg n) e δ ∧
      (∀ k, (δ k : ℤ) = (τ • a) k + d k) ∧ aeval y e = s * ∏ k, y ⟨k, c k⟩ ^ d k := by
  have hx : s * ∏ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * a k)) ∈ Geo.chartRingZ (ι := blockIdx n) y c := hs c hc
  obtain ⟨δ', e', he', hv'⟩ := exists_form_of_mem_chartRingZ y c hc hx
  set ex : ι → ℕ := fun k => ((τ : ℤ) * a k + ((τ : ℤ) * a k).natAbs).toNat with hex
  have hexk : ∀ k, (ex k : ℤ) = (τ : ℤ) * a k + ((τ : ℤ) * a k).natAbs := fun k => by
    rw [hex]
    exact Int.toNat_of_nonneg (by omega)
  refine ⟨fun k => δ' k + ((τ : ℤ) * a k).natAbs, δ' + ex, e' * chartMonomial c ex,
    he'.mul (isWeightedHomogeneous_chartMonomial c ex), fun k => ?_, ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, nsmul_eq_mul, Nat.cast_add, hexk k]
    ring
  · rw [map_mul, hv', aeval_chartMonomial, mul_assoc, mul_assoc, ← Finset.prod_mul_distrib,
      ← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl fun k _ => ?_
    have h0 := hc k
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_natCast, ← zpow_add₀ h0, ← zpow_add₀ h0, hexk k]
    congr 1
    push_cast
    ring

end ChartLatSection

open ChartLatSection in

theorem ChartLatSection.proof : ChartLatSection.Statement := by
  intro ι _ _ n Ω _ y P a τ s hP
  constructor
  · intro hs
    obtain ⟨c₀, hc₀⟩ := P.exists_chart
    have hy₀ : ∀ k, y ⟨k, c₀ k⟩ ≠ 0 := fun k => (coord_notMem_iff y hP _).mp (hc₀ k)
    obtain ⟨d₀, δ₀, e₀, he₀, hδ₀, hv₀⟩ := exists_chartForm y a τ hs c₀ hy₀
    have hm₀ : ∏ k, y ⟨k, c₀ k⟩ ^ d₀ k ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hy₀ k)
    have hden : chartMonomial c₀ d₀ ∉ P.ideal := by
      rw [hP, form_mem_iff y (isWeightedHomogeneous_chartMonomial c₀ d₀), aeval_chartMonomial]
      exact hm₀
    refine ⟨⟨e₀, chartMonomial c₀ d₀, δ₀, d₀, he₀, isWeightedHomogeneous_chartMonomial c₀ d₀,
      fun k => by rw [hδ₀ k]; ring, hden, fun c hc => ?_⟩, ?_⟩
    · have hyc : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => (coord_notMem_iff y hP _).mp (hc k)
      obtain ⟨d, δ, e, he, hδ, hv⟩ := exists_chartForm y a τ hs c hyc
      refine ⟨d, e, ⟨δ, he, hδ⟩, ?_⟩
      have hdeg : d₀ + δ = δ₀ + d := by
        funext k
        have h1 := hδ k
        have h2 := hδ₀ k
        simp only [Pi.add_apply]
        omega
      have hhom : IsWeightedHomogeneous (coordDeg n)
          (chartMonomial c₀ d₀ * e - e₀ * chartMonomial c d) (d₀ + δ) := by
        refine ((isWeightedHomogeneous_chartMonomial c₀ d₀).mul he).sub ?_
        rw [hdeg]
        exact he₀.mul (isWeightedHomogeneous_chartMonomial c d)
      rw [hP, form_mem_iff y hhom, map_sub, map_mul, map_mul, hv, hv₀, aeval_chartMonomial,
        aeval_chartMonomial]
      ring
    · intro g h δg δh hg hh hd
      have hmk : P.mkF (chartMonomial c₀ d₀) ≠ 0 := by
        rw [Ne, P.mkF_eq_zero_iff]
        exact hden
      have hdeg : δg + d₀ = δ₀ + δh := by
        funext k
        have h1 := hd k
        have h2 := hδ₀ k
        simp only [Pi.add_apply, Pi.smul_apply, nsmul_eq_mul] at h1 h2 ⊢
        omega
      have hhom : IsWeightedHomogeneous (coordDeg n) (g * chartMonomial c₀ d₀ - e₀ * h) (δg + d₀) := by
        refine (hg.mul (isWeightedHomogeneous_chartMonomial c₀ d₀)).sub ?_
        rw [hdeg]
        exact he₀.mul hh
      have key : P.mkF g = P.mkF e₀ / P.mkF (chartMonomial c₀ d₀) * P.mkF h ↔
          g * chartMonomial c₀ d₀ - e₀ * h ∈ P.ideal := by
        rw [← P.mkF_eq_zero_iff, map_sub, map_mul, map_mul, sub_eq_zero, div_mul_eq_mul_div,
          eq_div_iff hmk]
      show _ ↔ P.mkF g = P.mkF e₀ / P.mkF (chartMonomial c₀ d₀) * P.mkF h
      rw [key, hP, form_mem_iff y hhom, map_sub, map_mul, map_mul, hv₀, aeval_chartMonomial,
        sub_eq_zero]
      constructor
      · intro h1
        rw [h1]
        ring
      · intro h1
        apply mul_right_cancel₀ hm₀
        linear_combination h1
  · rintro ⟨t, ht⟩
    have hyP : ∀ f ∈ P.ideal, aeval y f = 0 := fun f hf => aeval_eq_zero_of_mem y (hP ▸ hf)
    have hG : aeval y t.den ≠ 0 := by
      intro h0
      exact t.den_not_mem (by rw [hP, form_mem_iff y t.den_isHomogeneous]; exact h0)
    have hmk : P.mkF t.den ≠ 0 := by
      rw [Ne, P.mkF_eq_zero_iff]
      exact t.den_not_mem
    have hread : aeval y t.num = s * aeval y t.den := by
      refine (ht t.num t.den t.numDeg t.denDeg t.num_isHomogeneous t.den_isHomogeneous
        (fun k => by have := t.deg_eq k; linarith)).mpr ?_
      show P.mkF t.num = P.mkF t.num / P.mkF t.den * P.mkF t.den
      rw [div_mul_cancel₀ _ hmk]
    have hs : s = aeval y t.num / aeval y t.den := by
      rw [hread, mul_div_assoc, div_self hG, mul_one]
    have hmem := t.value_mem_chartLat y hyP hG
    rw [← hs] at hmem
    intro c hc
    have h := hmem c hc
    have he : ∀ k, -(((1 : ℕ) : ℤ) * (τ • a) k) = -((τ : ℤ) * a k) := fun k => by
      simp
    simp only [he] at h
    exact h

end

end GroundTheory.Heights₂.Heights
