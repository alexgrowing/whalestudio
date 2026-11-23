import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.Doubling

namespace GlobalTheory.LocalNormProd

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

theorem exists_nnnorm_eq_zpow (x : Fv F v) (hx : x ≠ 0) :
    ∃ n : ℤ, ‖x‖₊ = (Ideal.absNorm v.asIdeal : ℝ≥0) ^ n := by
  have h0 : (Valued.v x : WithZero (Multiplicative ℤ)) ≠ 0 := (Valuation.ne_zero_iff _).mpr hx
  refine ⟨Multiplicative.toAdd (WithZero.unzero h0), ?_⟩
  rw [← WithZeroMulInt.toNNReal_neg_apply (NumberField.HeightOneSpectrum.absNorm_ne_zero v) h0]
  exact NNReal.eq (NumberField.FinitePlace.norm_def v x)

theorem exists_nnnorm_eq_inv_pow (x : Fv F v) (hx : x ≠ 0) (h1 : ‖x‖₊ ≤ 1) :
    ∃ e : ℕ, ‖x‖₊ = ((Ideal.absNorm v.asIdeal : ℝ≥0) ^ e)⁻¹ := by
  obtain ⟨n, hn⟩ := exists_nnnorm_eq_zpow v x hx
  have hq := NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v
  rw [hn, zpow_le_one_iff_right₀ hq] at h1
  refine ⟨(-n).toNat, ?_⟩
  rw [hn, ← zpow_natCast, ← zpow_neg, Int.toNat_of_nonneg (by omega), neg_neg]

theorem natCast_eq_embedding (n : ℕ) :
    (n : Fv F v) = NumberField.FinitePlace.embedding v (algebraMap (𝓞 F) F (n : 𝓞 F)) := by
  simp only [map_natCast]

theorem nnnorm_natCast_le_one (n : ℕ) : ‖(n : Fv F v)‖₊ ≤ 1 := by
  rw [natCast_eq_embedding]
  exact NumberField.FinitePlace.norm_le_one F v _

theorem nnnorm_absNorm_le :
    ‖((Ideal.absNorm v.asIdeal : ℕ) : Fv F v)‖₊ ≤ (Ideal.absNorm v.asIdeal : ℝ≥0)⁻¹ := by
  have hq := NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v
  have hlt : ‖((Ideal.absNorm v.asIdeal : ℕ) : Fv F v)‖₊ < 1 := by
    rw [natCast_eq_embedding]
    exact (NumberField.FinitePlace.norm_lt_one_iff_mem F v _).mpr (Ideal.absNorm_mem _)
  by_cases hx : ((Ideal.absNorm v.asIdeal : ℕ) : Fv F v) = 0
  · rw [hx]; simp
  obtain ⟨n, hn⟩ := exists_nnnorm_eq_zpow v _ hx
  rw [hn, zpow_lt_one_iff_right₀ hq] at hlt
  rw [hn, ← zpow_neg_one]
  exact zpow_le_zpow_right₀ hq.le (by omega)

end GlobalTheory.LocalNormProd

namespace GlobalTheory

open LocalNormProd in

theorem exists_nat_finprod_nnnorm_eq_inv :
    ∀ (F : Type) [Field F] [NumberField F] (c : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v), (∀ v, c v ≠ 0) → (∀ v, ‖c v‖₊ ≤ 1) →
    (Function.mulSupport fun v => ‖c v‖₊).Finite →
    ∃ m : ℕ, 0 < m ∧ (∏ᶠ v, ‖c v‖₊) = (m : ℝ≥0)⁻¹ ∧ ∀ v, ‖(m : Fv F v)‖₊ ≤ ‖c v‖₊ := by
  classical
  intro F _ _ c h0 h1 hfin
  choose e he using fun v => exists_nnnorm_eq_inv_pow v (c v) (h0 v) (h1 v)
  refine ⟨∏ v ∈ hfin.toFinset, Ideal.absNorm v.asIdeal ^ e v, ?_, ?_, ?_⟩
  · exact Finset.prod_pos fun v _ =>
      pow_pos (zero_lt_one.trans (NumberField.HeightOneSpectrum.one_lt_absNorm v)) _
  · rw [finprod_eq_prod_of_mulSupport_subset _ (s := hfin.toFinset) (by simp)]
    push_cast
    rw [← Finset.prod_inv_distrib]
    exact Finset.prod_congr rfl fun v _ => he v
  · intro v
    by_cases hv : v ∈ hfin.toFinset
    · rw [← Finset.mul_prod_erase _ _ hv, Nat.cast_mul, nnnorm_mul, he v, Nat.cast_pow, nnnorm_pow,
        ← inv_pow]
      exact (mul_le_of_le_one_right' (nnnorm_natCast_le_one v _)).trans
        (pow_le_pow_left' (nnnorm_absNorm_le v) _)
    · have : ‖c v‖₊ = 1 := by simpa using hv
      rw [this]
      exact nnnorm_natCast_le_one v _

end GlobalTheory
