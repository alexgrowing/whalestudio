import Mathlib
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterUnramifiedAeAndExistsLevel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNatCongrOfAbsNormPrime
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsAbsoluteValueOfIsDiscreteValuationRing
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuationPowSubPowLe

open NumberField IsDedekindDomain Formalism.L2.Host IsLocalRing Polynomial

namespace GlobalTheory.Mem.WildChar

theorem le_exp_neg_one_of_lt_one {g : WithZero (Multiplicative ℤ)} (hy : g < 1) :
    g ≤ WithZero.exp (-1 : ℤ) := by
  by_cases hg : g = 0
  · rw [hg]; exact zero_le
  · rw [← WithZero.exp_log hg] at hy ⊢
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at hy
    rw [WithZero.exp_le_exp]
    omega

theorem val_pow_sub_pow_le {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ]
    (w : Valuation K Γ) {a b : K} (ha : w a ≤ 1) (hb : w b ≤ 1) (m : ℕ) :
    w (a ^ m - b ^ m) ≤ w (a - b) := by
  first
  | exact @_root_.GlobalTheory.ValuationPowSubPow.valuation_pow_sub_pow_le
  | exact _root_.GlobalTheory.ValuationPowSubPow.valuation_pow_sub_pow_le
  | (apply _root_.GlobalTheory.ValuationPowSubPow.valuation_pow_sub_pow_le <;> assumption)
  | (intros; apply _root_.GlobalTheory.ValuationPowSubPow.valuation_pow_sub_pow_le <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ValuationPowSubPow.valuation_pow_sub_pow_le <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ValuationPowSubPow.valuation_pow_sub_pow_le ..)

theorem val_pow_sub_one_le {K : Type*} [Field K] (w : Valuation K (WithZero (Multiplicative ℤ)))
    {u : K} (hu : w u ≤ 1) (hu1 : w (u - 1) < 1) {q : ℕ} (hq : w (q : K) < 1) :
    w (u ^ q - 1) ≤ w (u - 1) * WithZero.exp (-1 : ℤ) := by
  rw [← mul_geom_sum, map_mul]
  refine mul_le_mul_right (le_exp_neg_one_of_lt_one ?_) _
  have e : ∑ i ∈ Finset.range q, u ^ i = (q : K) + ∑ i ∈ Finset.range q, (u ^ i - 1 ^ i) := by
    simp
  rw [e]
  refine Valuation.map_add_lt _ hq (Valuation.map_sum_lt _ one_ne_zero fun i _ => ?_)
  exact (val_pow_sub_pow_le w hu (map_one w).le i).trans_lt hu1

theorem val_pow_pow_sub_one_le {K : Type*} [Field K] (w : Valuation K (WithZero (Multiplicative ℤ)))
    {u : K} (hu : w u ≤ 1) (hu1 : w (u - 1) < 1) {q : ℕ} (hq : w (q : K) < 1) (n : ℕ) :
    w (u ^ (q ^ n) - 1) ≤ WithZero.exp (-(n : ℤ)) := by
  induction n with
  | zero => simpa using hu1.le
  | succ n ih =>
    have h1 : w (u ^ (q ^ n)) ≤ 1 := by rw [map_pow]; exact pow_le_one' hu _
    have h2 : w (u ^ (q ^ n) - 1) < 1 := by
      have := val_pow_sub_pow_le w hu (map_one w).le (q ^ n)
      rw [one_pow] at this
      exact this.trans_lt hu1
    rw [pow_succ, pow_mul]
    refine (val_pow_sub_one_le w h1 h2 hq).trans ((mul_le_mul_left ih _).trans (le_of_eq ?_))
    rw [← WithZero.exp_add]
    congr 1
    push_cast
    ring

variable {L : Type} [Field L] [NumberField L] (v : HeightOneSpectrum (𝓞 L))

theorem valued_algebraMap_lt_one {y : 𝓞 L} :
    Valued.v (algebraMap (𝓞 L) (v.adicCompletion L) y) < 1 ↔ y ∈ v.asIdeal := by
  have h3 : Valued.v (algebraMap (𝓞 L) (v.adicCompletion L) y)
      = v.valuation L (algebraMap (𝓞 L) L y) :=
    ReciprocityTheory.Aut.adic_valued_algebraMap v (algebraMap (𝓞 L) L y)
  rw [h3]
  exact HeightOneSpectrum.valuation_lt_one_iff_mem v _

theorem valued_absNorm_lt_one :
    Valued.v ((Ideal.absNorm v.asIdeal : ℕ) : v.adicCompletion L) < 1 := by
  rw [← map_natCast (algebraMap (𝓞 L) (v.adicCompletion L)), valued_algebraMap_lt_one]
  exact Ideal.absNorm_mem v.asIdeal

theorem one_lt_absNorm : 1 < Ideal.absNorm v.asIdeal := by
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]; exact v.isPrime.ne_top
  omega

theorem valued_pow_sub_one_lt_one {x : v.adicCompletion L} (hx : Valued.v x = 1) :
    Valued.v (x ^ (Ideal.absNorm v.asIdeal - 1) - 1) < 1 := by
  obtain ⟨y, hy⟩ := ReciprocityTheory.Aut.adic_exists_approx v x hx.le
  have hy1 : Valued.v (algebraMap (𝓞 L) (v.adicCompletion L) y) = 1 := by
    rw [← hx]
    apply Valuation.map_eq_of_sub_lt
    rw [Valuation.map_sub_swap, hx]
    exact hy
  have hnot : y ∉ v.asIdeal := by
    rw [← valued_algebraMap_lt_one, hy1]; exact lt_irrefl _
  have hmem : y ^ (Ideal.absNorm v.asIdeal - 1) - 1 ∈ v.asIdeal := by
    haveI := v.isMaximal
    letI := Ideal.Quotient.field v.asIdeal
    haveI : Finite (𝓞 L ⧸ v.asIdeal) := v.asIdeal.finiteQuotientOfFreeOfNeBot v.ne_bot
    letI := Fintype.ofFinite (𝓞 L ⧸ v.asIdeal)
    rw [← Ideal.Quotient.eq, map_pow, map_one, Ideal.absNorm_apply, Submodule.cardQuot_apply,
      Nat.card_eq_fintype_card]
    exact FiniteField.pow_card_sub_one_eq_one _ (fun h => hnot (Ideal.Quotient.eq_zero_iff_mem.1 h))
  rw [← valued_algebraMap_lt_one, map_sub, map_pow, map_one] at hmem
  rw [← sub_add_sub_cancel _
    (algebraMap (𝓞 L) (v.adicCompletion L) y ^ (Ideal.absNorm v.asIdeal - 1))]
  exact Valuation.map_add_lt _ ((val_pow_sub_pow_le _ hx.le hy1.le _).trans_lt hy) hmem

theorem mem_maximalIdeal_iff (a : v.adicCompletionIntegers L) :
    a ∈ maximalIdeal (v.adicCompletionIntegers L) ↔ Valued.v (a : v.adicCompletion L) < 1 := by
  rw [mem_maximalIdeal, mem_nonunits_iff,
    HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]
  have h : Valued.v (a : v.adicCompletion L) ≤ 1 := a.2
  exact ⟨fun h' => lt_of_le_of_ne h h', fun h' => h'.ne⟩

theorem exists_rootOfUnity_congr {x : v.adicCompletion L} (hx : Valued.v x = 1) :
    ∃ ζ : v.adicCompletion L, ζ ^ (Ideal.absNorm v.asIdeal - 1) = 1 ∧ Valued.v (ζ - x) < 1 := by
  have hc : IsAdicComplete (maximalIdeal (v.adicCompletionIntegers L))
      (v.adicCompletionIntegers L) := by
    refine NormIntegers.isAdicComplete_of_fg (C := v.adicCompletion L) ⟨?_, ?_, ?_⟩
      (IsNoetherian.noetherian _) (maximalIdeal.isMaximal _).ne_top
    · exact FaithfulSMul.algebraMap_injective _ _
    · intro x
      have : ‖(x : v.adicCompletion L)‖ ≤ 1 := Valued.toNormedField.norm_le_one_iff.2 x.2
      exact_mod_cast this
    · intro x hx
      have : ‖x‖ ≤ 1 := by exact_mod_cast hx
      exact ⟨⟨x, Valued.toNormedField.norm_le_one_iff.1 this⟩, rfl⟩
  have hq := one_lt_absNorm v
  let a : v.adicCompletionIntegers L := ⟨x, hx.le⟩
  obtain ⟨ζ, h1, h2⟩ := HenselianRing.is_henselian (I := maximalIdeal (v.adicCompletionIntegers L))
    (X ^ (Ideal.absNorm v.asIdeal - 1) - C 1) (monic_X_pow_sub_C _ (by omega)) a
    (by
      rw [mem_maximalIdeal_iff]
      simpa [a] using valued_pow_sub_one_lt_one v hx)
    (by
      apply IsUnit.map
      rw [HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]
      have h3 : Valued.v (((Ideal.absNorm v.asIdeal - 1 : ℕ)) : v.adicCompletion L) = 1 := by
        rw [Nat.cast_sub hq.le, Nat.cast_one, Valuation.map_sub_swap]
        exact Valuation.map_one_sub_of_lt _ (valued_absNorm_lt_one v)
      simp [a, derivative_X_pow, hx, h3])
  refine ⟨ζ, ?_, ?_⟩
  · have h4 : ζ ^ (Ideal.absNorm v.asIdeal - 1) = 1 := by
      simpa [sub_eq_zero] using h1
    have h5 := congrArg (algebraMap (v.adicCompletionIntegers L) (v.adicCompletion L)) h4
    rw [map_pow, map_one] at h5
    exact h5
  · have h6 := (mem_maximalIdeal_iff v _).1 h2
    rw [AddSubgroupClass.coe_sub] at h6
    exact h6

theorem orders_on_units : ∀ (L : Type) [Field L] [NumberField L] (χ : HChar L) (v : HeightOneSpectrum (𝓞 L)), (χ.TameAt v → ∀ x, IsUnitAt v x → χ.loc v x ^ (Ideal.absNorm v.asIdeal - 1) = 1) ∧ ((∀ x : (v.adicCompletion L)ˣ, x ^ (Ideal.absNorm v.asIdeal - 1) = 1 → χ.loc v x = 1) → ∀ x, IsUnitAt v x → ∃ n : ℕ, χ.loc v x ^ (Ideal.absNorm v.asIdeal ^ n) = 1) := by
  intro L _ _ χ v
  refine ⟨fun h x hx => ?_, fun h x hx => ?_⟩
  · rw [← map_pow]
    refine h _ (GlobalTheory.Mem.UnrAe.isUnitAt_pow hx _) ?_
    rw [Units.val_pow_eq_pow_val]
    simpa using le_exp_neg_one_of_lt_one (valued_pow_sub_one_lt_one v hx)
  · obtain ⟨n, hn⟩ := GlobalTheory.Mem.UnrAe.exists_levelLe χ v
    have hx' : Valued.v (x : v.adicCompletion L) = 1 := hx
    obtain ⟨ζ, h1, h2⟩ := exists_rootOfUnity_congr v hx'
    have hζ : Valued.v ζ = 1 := by
      rw [← hx']
      apply Valuation.map_eq_of_sub_lt
      rwa [hx']
    have h0 : ζ ≠ 0 := by
      rintro rfl
      simp at hζ
    let z : (v.adicCompletion L)ˣ := Units.mk0 ζ h0
    have hz : χ.loc v z = 1 := h z (Units.ext (by simpa [z] using h1))
    have hu : IsUnitAt v (x * z⁻¹) := by
      simp [IsUnitAt, z, hx', hζ]
    have hu1 : Valued.v (((x * z⁻¹ : (v.adicCompletion L)ˣ) : v.adicCompletion L) - 1) < 1 := by
      have e : ((x * z⁻¹ : (v.adicCompletion L)ˣ) : v.adicCompletion L) - 1 = (x - ζ) * ζ⁻¹ := by
        simp [z, sub_mul, h0]
      rw [e, map_mul, map_inv₀, hζ, inv_one, mul_one, Valuation.map_sub_swap]
      exact h2
    refine ⟨n, ?_⟩
    have h3 := hn _ (GlobalTheory.Mem.UnrAe.isUnitAt_pow hu (Ideal.absNorm v.asIdeal ^ n)) (by
      rw [Units.val_pow_eq_pow_val]
      exact val_pow_pow_sub_one_le _ (le_of_eq hu) hu1 (valued_absNorm_lt_one v) n)
    rwa [map_pow, map_mul, map_inv, hz, inv_one, mul_one] at h3

end GlobalTheory.Mem.WildChar
