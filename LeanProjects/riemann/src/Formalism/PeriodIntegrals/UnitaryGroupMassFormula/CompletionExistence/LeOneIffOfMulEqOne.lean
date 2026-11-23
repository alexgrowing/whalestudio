import Mathlib
import Formalism.LocalToGlobal.AdelicCompactOpens.UniROfUniRT

noncomputable section

namespace PI.CompAtExist

open NumberField IsDedekindDomain ReciprocityTheory.Aut

def StepA (L : Type) [Field L] [NumberField L] [IsCMField L] : Prop :=
  ∀ (s : SplitPlace L) (k : L),
    Valued.v (s.i k) = Valued.v (algebraMap L (s.w.adicCompletion L) k)

theorem val_eq_of_le_one_iff {K : Type*} [Field K] (μ ν : Valuation K (WithZero (Multiplicative ℤ)))
    (h : ∀ x, μ x ≤ 1 ↔ ν x ≤ 1) {ϖ π : K} (hϖ : ν ϖ = WithZero.exp (-1))
    (hπ : μ π = WithZero.exp (-1)) (x : K) : μ x = ν x := by
  have hunit : ∀ (μ' ν' : Valuation K (WithZero (Multiplicative ℤ))), (∀ x, μ' x ≤ 1 ↔ ν' x ≤ 1) →
      ∀ y, ν' y = 1 → μ' y = 1 := by
    intro μ' ν' h' y hy
    have hy0 : y ≠ 0 := by
      rintro rfl
      simp at hy
    have h1 : μ' y ≤ 1 := (h' y).2 hy.le
    have h2 : μ' y⁻¹ ≤ 1 := (h' y⁻¹).2 (by rw [map_inv₀, hy, inv_one])
    have hm : μ' y⁻¹ * μ' y = 1 := by rw [← map_mul, inv_mul_cancel₀ hy0, map_one]
    have hle : μ' y⁻¹ * μ' y ≤ 1 * μ' y := mul_le_mul' h2 le_rfl
    rw [hm, one_mul] at hle
    exact le_antisymm h1 hle
  have hϖ0 : ϖ ≠ 0 := by
    rintro rfl
    rw [map_zero] at hϖ
    exact WithZero.exp_ne_zero hϖ.symm
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [map_zero] at hπ
    exact WithZero.exp_ne_zero hπ.symm
  have key : ∀ y, y ≠ 0 → μ y * μ ϖ ^ (WithZero.log (ν y)) = 1 := by
    intro y hy
    have hνy : ν y ≠ 0 := ν.ne_zero_iff.2 hy
    have hνp : ν (ϖ ^ (WithZero.log (ν y))) ≠ 0 := ν.ne_zero_iff.2 (zpow_ne_zero _ hϖ0)
    have hne : ν (y * ϖ ^ (WithZero.log (ν y))) ≠ 0 := ν.ne_zero_iff.2 (mul_ne_zero hy (zpow_ne_zero _ hϖ0))
    have h1 : ν (y * ϖ ^ (WithZero.log (ν y))) = 1 := by
      rw [← WithZero.exp_log hne, map_mul, WithZero.log_mul hνy hνp,
        map_zpow₀, WithZero.log_zpow, hϖ, WithZero.log_exp, smul_eq_mul]
      rw [show WithZero.log (ν y) + WithZero.log (ν y) * (-1) = 0 by ring, WithZero.exp_zero]
    have h2 := hunit μ ν h _ h1
    rwa [map_mul, map_zpow₀] at h2
  have hμϖ0 : μ ϖ ≠ 0 := μ.ne_zero_iff.2 hϖ0
  have hμϖ : μ ϖ = WithZero.exp (-1) := by
    have k1 := congrArg WithZero.log (key π hπ0)
    rw [WithZero.log_mul (by rw [hπ]; exact WithZero.exp_ne_zero) (zpow_ne_zero _ hμϖ0), hπ,
      WithZero.log_exp, WithZero.log_zpow, WithZero.log_one, smul_eq_mul] at k1
    have hij : WithZero.log (ν π) * WithZero.log (μ ϖ) = 1 := by linarith
    have hlt : μ ϖ < 1 := by
      refine lt_of_le_of_ne ((h ϖ).2 (by rw [hϖ]; exact WithZero.exp_le_exp.2 (by norm_num))) ?_
      intro h1
      have := hunit ν μ (fun x => (h x).symm) ϖ h1
      rw [hϖ] at this
      have := congrArg WithZero.log this
      rw [WithZero.log_exp, WithZero.log_one] at this
      norm_num at this
    have hneg : WithZero.log (μ ϖ) < 0 := by
      have := (WithZero.log_le_log hμϖ0 one_ne_zero).2 hlt.le
      rw [WithZero.log_one] at this
      rcases lt_or_eq_of_le this with h' | h'
      · exact h'
      · exfalso
        have := WithZero.exp_log hμϖ0
        rw [h', WithZero.exp_zero] at this
        exact hlt.ne this.symm
    rcases Int.eq_one_or_neg_one_of_mul_eq_one (by rw [mul_comm]; exact hij) with h' | h'
    · omega
    · rw [← WithZero.exp_log hμϖ0, h']
  by_cases hx : x = 0
  · rw [hx, map_zero, map_zero]
  · have hμx : μ x ≠ 0 := μ.ne_zero_iff.2 hx
    have hνx : ν x ≠ 0 := ν.ne_zero_iff.2 hx
    have k2 := congrArg WithZero.log (key x hx)
    rw [WithZero.log_mul hμx (zpow_ne_zero _ hμϖ0), hμϖ, WithZero.log_zpow, WithZero.log_exp,
      WithZero.log_one, smul_eq_mul] at k2
    rw [← WithZero.exp_log hμx, ← WithZero.exp_log hνx]
    congr 1
    linarith

section

variable {L : Type} [Field L] [NumberField L] [IsCMField L]

def muV (s : SplitPlace L) : Valuation L (WithZero (Multiplicative ℤ)) :=
  (Valued.v : Valuation (s.v.adicCompletion (maximalRealSubfield L)) (WithZero (Multiplicative ℤ))).comap
    (s.i : L →+* s.v.adicCompletion (maximalRealSubfield L))

theorem muV_apply (s : SplitPlace L) (k : L) : muV s k = Valued.v (s.i k) := rfl

theorem muV_int_le_one (s : SplitPlace L) (r : 𝓞 L) : muV s (algebraMap (𝓞 L) L r) ≤ 1 := by
  rw [muV_apply]
  have := s.split_le_one r
  rwa [RingOfIntegers.coe_eq_algebraMap] at this

theorem muV_int_lt_one_iff (s : SplitPlace L) (r : 𝓞 L) :
    muV s (algebraMap (𝓞 L) L r) < 1 ↔ r ∈ s.w.asIdeal := by
  rw [muV_apply, show s.w.asIdeal = s.ideal from rfl, s.split_mem_ideal, RingOfIntegers.coe_eq_algebraMap]

theorem muV_int_eq_one_iff (s : SplitPlace L) (r : 𝓞 L) :
    muV s (algebraMap (𝓞 L) L r) = 1 ↔ r ∉ s.w.asIdeal := by
  rw [← muV_int_lt_one_iff, not_lt]
  exact ⟨fun h => h.ge, fun h => le_antisymm (muV_int_le_one s r) h⟩

private theorem exists_ringOfIntegers_not_mem_mul_eq_of_valuation_le (s : SplitPlace L) (x : L) (hx : s.w.valuation L x ≤ 1) :
    ∃ c t : 𝓞 L, c ∉ s.w.asIdeal ∧ algebraMap (𝓞 L) L c * x = algebraMap (𝓞 L) L t := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 L) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hbL : algebraMap (𝓞 L) L b ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 L) L)).2 hb0
  have hvb : s.w.intValuation b ≠ 0 := s.w.intValuation_ne_zero b hb0
  rw [map_div₀, s.w.valuation_of_algebraMap, s.w.valuation_of_algebraMap] at hx
  have hab : s.w.intValuation a ≤ s.w.intValuation b := (div_le_one₀ (zero_lt_iff.2 hvb)).1 hx
  have hk0 : WithZero.log (s.w.intValuation b) ≤ 0 := by
    have := (WithZero.log_le_log hvb one_ne_zero).2 (s.w.intValuation_le_one b)
    rwa [WithZero.log_one] at this
  have hbe : s.w.intValuation b = WithZero.exp (-(((-WithZero.log (s.w.intValuation b)).toNat : ℕ) : ℤ)) := by
    rw [Int.toNat_of_nonneg (by omega), neg_neg, WithZero.exp_log hvb]
  set e : ℕ := (-WithZero.log (s.w.intValuation b)).toNat with he
  have ha_mem : a ∈ s.w.asIdeal ^ e := (s.w.intValuation_le_pow_iff_mem a e).1 (hab.trans hbe.le)
  have hb_mem : b ∈ s.w.asIdeal ^ e := (s.w.intValuation_le_pow_iff_mem b e).1 hbe.le
  have hb_not : b ∉ s.w.asIdeal ^ (e + 1) := by
    rw [← s.w.intValuation_le_pow_iff_mem, hbe, WithZero.exp_le_exp]
    push_cast
    omega
  obtain ⟨J, hJ⟩ : s.w.asIdeal ^ e ∣ Ideal.span {b} :=
    Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hb_mem)
  have hJw : ¬ J ≤ s.w.asIdeal := by
    intro hle
    apply hb_not
    have : Ideal.span {b} ≤ s.w.asIdeal ^ (e + 1) := by
      rw [hJ, pow_succ]
      exact Ideal.mul_mono_right hle
    exact (Ideal.span_singleton_le_iff_mem _).1 this
  obtain ⟨c, hcJ, hcw⟩ := SetLike.not_le_iff_exists.1 hJw
  have hca : a * c ∈ Ideal.span {b} := by
    rw [hJ]
    exact Ideal.mul_mem_mul ha_mem hcJ
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 hca
  refine ⟨c, t, hcw, ?_⟩
  rw [mul_div_assoc', div_eq_iff hbL, ← map_mul, ← map_mul, ht, mul_comm]

theorem muV_le_one_iff (s : SplitPlace L) (x : L) : muV s x ≤ 1 ↔ s.w.valuation L x ≤ 1 := by
  have hμint : ∀ r : 𝓞 L, r ∉ s.w.asIdeal → muV s (algebraMap (𝓞 L) L r) = 1 :=
    fun r hr => (muV_int_eq_one_iff s r).2 hr
  have hνint : ∀ r : 𝓞 L, r ∉ s.w.asIdeal → s.w.valuation L (algebraMap (𝓞 L) L r) = 1 := by
    intro r hr
    rw [s.w.valuation_of_algebraMap]
    exact le_antisymm (s.w.intValuation_le_one r)
      (not_lt.1 fun h => hr ((s.w.intValuation_lt_one_iff_mem r).1 h))
  constructor
  · intro hμ
    by_contra hν
    push_neg at hν
    have hx0 : x ≠ 0 := by
      rintro rfl
      simp at hν
    have hν' : s.w.valuation L x⁻¹ ≤ 1 := by
      rw [map_inv₀]
      exact inv_le_one_of_one_le₀ hν.le
    obtain ⟨c, t, hc, ht⟩ := exists_ringOfIntegers_not_mem_mul_eq_of_valuation_le s x⁻¹ hν'
    have hνt : s.w.valuation L (algebraMap (𝓞 L) L t) < 1 := by
      rw [← ht, map_mul, hνint c hc, one_mul, map_inv₀]
      exact inv_lt_one_of_one_lt₀ hν
    have htw : t ∈ s.w.asIdeal := by
      rw [s.w.valuation_of_algebraMap] at hνt
      exact (s.w.intValuation_lt_one_iff_mem t).1 hνt
    have hμt : muV s (algebraMap (𝓞 L) L t) < 1 := (muV_int_lt_one_iff s t).2 htw
    rw [← ht, map_mul, hμint c hc, one_mul, map_inv₀] at hμt
    have hμx0 : muV s x ≠ 0 := (muV s).ne_zero_iff.2 hx0
    have h1 := (inv_lt_one₀ (zero_lt_iff.2 hμx0)).1 hμt
    exact absurd hμ (not_le.2 h1)
  · intro hν
    obtain ⟨c, t, hc, ht⟩ := exists_ringOfIntegers_not_mem_mul_eq_of_valuation_le s x hν
    have h1 := muV_int_le_one s t
    rw [← ht, map_mul, hμint c hc, one_mul] at h1
    exact h1

theorem muV_eq (s : SplitPlace L) (x : L) : muV s x = s.w.valuation L x := by
  obtain ⟨ϖ, hϖ⟩ := IsDedekindDomain.HeightOneSpectrum.valuation_exists_uniformizer L s.w
  obtain ⟨a, ha⟩ := IsDedekindDomain.HeightOneSpectrum.intValuation_exists_uniformizer s.v
  refine val_eq_of_le_one_iff (muV s) (s.w.valuation L) (muV_le_one_iff s) hϖ
    (π := ((algebraMap (𝓞 (maximalRealSubfield L)) (𝓞 L) a : 𝓞 L) : L)) ?_ x
  rw [muV_apply, s.split_val_alg, RingOfIntegers.coe_eq_algebraMap, s.v.valuation_of_algebraMap, ha]

theorem stepA : StepA L := by
  intro s k
  rw [← muV_apply, muV_eq]
  exact (IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' s.w k).symm

end

end PI.CompAtExist
