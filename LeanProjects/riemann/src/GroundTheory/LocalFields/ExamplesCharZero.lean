import Mathlib
import GroundTheory.LocalFields.Examples

namespace GroundTheory.LocalField

open ValuativeRel WithZero Topology

namespace CharZero

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

instance fact_prime_ringChar : Fact (ringChar 𝓀[K]).Prime :=
  ⟨CharP.char_is_prime 𝓀[K] (ringChar 𝓀[K])⟩

variable (p : ℕ) [CharP 𝓀[K] p]

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in

theorem valuation_intCast_le_one (n : ℤ) : valuation K (n : K) ≤ 1 :=
  (Valuation.mem_integer_iff _ _).mp (intCast_mem _ n)

theorem valuation_intCast_eq_one_iff (n : ℤ) : valuation K (n : K) = 1 ↔ ¬ (p : ℤ) ∣ n := by
  have hres : IsLocalRing.residue 𝒪[K] (n : 𝒪[K]) = (n : 𝓀[K]) := map_intCast _ n
  rw [← CharP.intCast_eq_zero_iff 𝓀[K] p n, ← hres, IsLocalRing.residue_eq_zero_iff,
    IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    Valuation.Integer.not_isUnit_iff_valuation_lt_one]
  push_cast
  constructor
  · intro h
    simp [h]
  · intro h
    exact le_antisymm (valuation_intCast_le_one K n) (not_lt.mp h)

variable [Fact p.Prime]

omit [Fact p.Prime] in

theorem valuation_p_lt_one : valuation K (p : K) < 1 := by
  refine lt_of_le_of_ne (by exact_mod_cast valuation_intCast_le_one K p) fun h => ?_
  have := (valuation_intCast_eq_one_iff K p p).mp (by exact_mod_cast h)
  exact this dvd_rfl

variable [CharZero K]

theorem valuation_ratCast_le_one_iff (q : ℚ) : valuation K (q : K) ≤ 1 ↔ ¬ p ∣ q.den := by
  have hden : (q.den : K) ≠ 0 := by exact_mod_cast q.den_ne_zero
  have hq : (q : K) = (q.num : K) / (q.den : K) := by
    rw [← Rat.cast_intCast, ← Rat.cast_natCast, ← Rat.cast_div, Rat.num_div_den]
  have hvden : valuation K (q.den : K) ≠ 0 := by simp
  rw [hq, map_div₀, div_le_one₀ (zero_lt_iff.mpr hvden)]
  constructor
  · intro h hp
    have hnum : ¬ (p : ℤ) ∣ q.num := by
      intro hn
      rw [Int.natCast_dvd] at hn
      exact Nat.not_coprime_of_dvd_of_dvd (Nat.Prime.one_lt Fact.out) hn hp q.reduced
    have h1 := (valuation_intCast_eq_one_iff K p q.num).mpr hnum
    obtain ⟨m, hm⟩ := hp
    have h2 : valuation K (q.den : K) < 1 := by
      rw [hm, Nat.cast_mul, map_mul]
      calc valuation K (p : K) * valuation K (m : K)
          ≤ valuation K (p : K) * 1 := by
            gcongr
            exact_mod_cast valuation_intCast_le_one K m
        _ < 1 := by simp [valuation_p_lt_one K p]
    rw [h1] at h
    exact absurd h (not_le.mpr h2)
  · intro hp
    have h1 : valuation K (q.den : K) = 1 := by
      have := (valuation_intCast_eq_one_iff K p q.den).mpr (by exact_mod_cast hp)
      exact_mod_cast this
    rw [h1]
    exact valuation_intCast_le_one K q.num

theorem isEquiv_comap_ratCast :
    ((valuation K).comap (Rat.castHom K)).IsEquiv (Rat.padicValuation p) :=
  Valuation.isEquiv_of_val_le_one fun q => by
    simp [valuation_ratCast_le_one_iff K p, Rat.padicValuation_le_one_iff]

section Embedding

noncomputable abbrev ratHom : WithVal (Rat.padicValuation p) →+* K :=
  (Rat.castHom K).comp (WithVal.equiv (Rat.padicValuation p)).toRingHom

theorem continuousAt_ratHom : ContinuousAt (ratHom K p) 0 := by
  rw [ContinuousAt, map_zero]
  refine ((IsValuativeTopology.hasBasis_nhds_zero' _).tendsto_iff
    (IsValuativeTopology.hasBasis_nhds_zero' K)).mpr fun γ hγ => ?_
  obtain ⟨n, hn⟩ := exists_pow_lt₀ (valuation_p_lt_one K p) (Units.mk0 γ hγ)
  set v := Rat.padicValuation p
  set t : WithVal v := (WithVal.equiv v).symm ((p : ℚ) ^ n)
  refine ⟨valuation (WithVal v) t, ?_, fun x hx => ?_⟩
  · simp [t, Nat.Prime.ne_zero Fact.out]
  · simp only [Set.mem_ofPred_eq] at hx ⊢
    have h1 := (ValuativeRel.isEquiv (valuation (WithVal v)) (WithVal.valuation v)).lt_iff_lt.mp hx
    have h2 : v (WithVal.equiv v x) < v ((p : ℚ) ^ n) := by simpa [t] using h1
    have h3 := (isEquiv_comap_ratCast K p).lt_iff_lt.mpr h2
    simp only [Valuation.comap_apply, Rat.coe_castHom] at h3
    calc valuation K (ratHom K p x) = valuation K ((WithVal.equiv v x : ℚ) : K) := rfl
      _ < valuation K (((p : ℚ) ^ n : ℚ) : K) := h3
      _ = valuation K (p : K) ^ n := by simp
      _ < γ := hn

section Uniform

local instance uniformSpaceK : UniformSpace K := IsTopologicalAddGroup.rightUniformSpace K

local instance isUniformAddGroupK : IsUniformAddGroup K := isUniformAddGroup_of_addCommGroup

theorem uniformContinuous_ratHom : UniformContinuous (ratHom K p) :=
  uniformContinuous_of_continuousAt_zero (ratHom K p) (continuousAt_ratHom K p)

noncomputable def padicHom : ℚ_[p] →+* K :=
  IsDenseInducing.extendRingHom Padic.isUniformInducing_cast_withVal
    Padic.isDenseInducing_cast_withVal.dense (uniformContinuous_ratHom K p)

theorem continuous_padicHom : Continuous (padicHom K p) :=
  (uniformContinuous_uniformly_extend Padic.isUniformInducing_cast_withVal
    Padic.isDenseInducing_cast_withVal.dense (uniformContinuous_ratHom K p)).continuous

end Uniform

theorem valuation_padicHom_padicInt_le_one (x : ℤ_[p]) :
    valuation K (padicHom K p (x : ℚ_[p])) ≤ 1 := by
  refine PadicInt.denseRange_intCast.induction_on x ?_ fun n => ?_
  · exact (Valuation.isClosed_integer (v := valuation K)).preimage
      ((continuous_padicHom K p).comp continuous_subtype_val)
  · simpa using valuation_intCast_le_one K n

theorem valuation_padicHom_le_one_iff (x : ℚ_[p]) :
    valuation K (padicHom K p x) ≤ 1 ↔ ‖x‖ ≤ 1 := by
  refine ⟨fun hv => ?_, fun hx => valuation_padicHom_padicInt_le_one K p ⟨x, hx⟩⟩
  by_contra hx
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hx
  have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Nat.Prime.ne_zero Fact.out)
  set y : ℚ_[p] := ((p : ℚ_[p]) * x)⁻¹
  have hxinv : ‖x⁻¹‖ ≤ (p : ℝ) ^ (-1 : ℤ) := by
    have : ‖x⁻¹‖ < (p : ℝ) ^ (0 : ℤ) := by
      rw [norm_inv, zpow_zero]
      exact inv_lt_one_of_one_lt₀ (not_le.mp hx)
    simpa using (Padic.norm_lt_pow_iff_norm_le_pow_sub_one x⁻¹ 0).mp this
  have hy : ‖y‖ ≤ 1 := by
    have hp : (0 : ℝ) < p := by exact_mod_cast (Nat.Prime.pos Fact.out)
    simp only [y, mul_inv, norm_mul, norm_inv, Padic.norm_p, inv_inv] at hxinv ⊢
    rw [zpow_neg_one] at hxinv
    calc (p : ℝ) * ‖x‖⁻¹ ≤ p * (p : ℝ)⁻¹ := by gcongr
      _ = 1 := mul_inv_cancel₀ hp.ne'
  have hvy := valuation_padicHom_padicInt_le_one K p ⟨y, hy⟩
  simp only at hvy
  have hone : padicHom K p x * padicHom K p y * padicHom K p p = 1 := by
    rw [← map_mul, ← map_mul]
    simp [y, hx0, hp0]
  have hvp : valuation K (padicHom K p p) < 1 := by
    simpa using valuation_p_lt_one K p
  have := congrArg (valuation K) hone
  rw [map_mul, map_mul, map_one] at this
  have h1 : valuation K (padicHom K p x) * valuation K (padicHom K p y) ≤ 1 :=
    mul_le_one' hv hvy
  have h2 := (mul_le_of_le_one_left' h1 : _ ≤ valuation K (padicHom K p p))
  exact absurd (this ▸ h2) (not_le.mpr hvp)

theorem isEquiv_comap_padicHom :
    ((valuation K).comap (padicHom K p)).IsEquiv Padic.mulValuation :=
  Valuation.isEquiv_of_val_le_one fun x => by
    rw [Valuation.comap_apply, valuation_padicHom_le_one_iff]
    simpa using (GroundTheory.LocalField.Padic.mulValuation_le_iff_norm_le p x 1).symm

theorem padicHom_vle_iff (a b : ℚ_[p]) : padicHom K p a ≤ᵥ padicHom K p b ↔ a ≤ᵥ b := by
  rw [Valuation.Compatible.vle_iff_le (v := valuation K),
    Valuation.Compatible.vle_iff_le (v := Padic.mulValuation)]
  simpa using (isEquiv_comap_padicHom K p).le_iff_le (x := a) (y := b)

theorem finiteDimensional_padicHom :
    letI := (padicHom K p).toAlgebra
    FiniteDimensional ℚ_[p] K := by
  let := (padicHom K p).toAlgebra
  have : T2Space K := by
    let := IsTopologicalAddGroup.rightUniformSpace K
    have := isUniformAddGroup_of_addCommGroup (G := K)
    infer_instance
  have : ContinuousSMul ℚ_[p] K :=
    ⟨((continuous_padicHom K p).comp continuous_fst).mul continuous_snd⟩
  exact FiniteDimensional.of_locallyCompactSpace ℚ_[p]

end Embedding

end CharZero

theorem exists_padic_finiteDimensional_of_charZero (K : Type*) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] [CharZero K] :
    ∃ (p : ℕ) (_ : Fact p.Prime) (_ : Algebra ℚ_[p] K), p = ringChar 𝓀[K] ∧
      ValuativeExtension ℚ_[p] K ∧ FiniteDimensional ℚ_[p] K ∧
        Continuous (algebraMap ℚ_[p] K) := by
  let alg := (CharZero.padicHom K (ringChar 𝓀[K])).toAlgebra
  exact ⟨ringChar 𝓀[K], inferInstance, alg, rfl, ⟨CharZero.padicHom_vle_iff K _⟩,
    CharZero.finiteDimensional_padicHom K _, CharZero.continuous_padicHom K _⟩

end GroundTheory.LocalField
