import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TransferIndices.DvTransferIdxOf

noncomputable section

namespace PI.Dv.TIW

open Formalism.BasicNotions NumberField IsDedekindDomain
open scoped WithZero

private theorem log_nonpos_of_le_one (m : ℤᵐ⁰) (h : m ≤ 1) : WithZero.log m ≤ 0 := by
  rcases eq_or_ne m 0 with h0 | h0
  · rw [h0, WithZero.log_zero]
  · rw [← WithZero.exp_log h0, ← WithZero.exp_zero] at h
    exact WithZero.exp_le_exp.mp h

theorem volume_nonneg : VNonneg := by
  intro K _ _ w x
  unfold vAdd
  have h := log_nonpos_of_le_one (w.valuation K (algebraMap (𝓞 K) K x)) (w.valuation_le_one x)
  omega

theorem mem_of_vAdd_ne {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) (x : 𝓞 K)
    (h : vAdd w (algebraMap (𝓞 K) K x) ≠ 0) : x ∈ w.asIdeal := by
  by_contra hx
  apply h
  have h1 : w.valuation K (algebraMap (𝓞 K) K x) = 1 :=
    le_antisymm (w.valuation_le_one x) (not_lt.mp fun hlt => hx ((w.valuation_lt_one_iff_mem x).mp hlt))
  unfold vAdd
  rw [h1, WithZero.log_one, neg_zero]

theorem volume_finite' : VFin := by
  intro K _ _ x hx
  have hI : Ideal.span {x} ≠ (0 : Ideal (𝓞 K)) := by
    rwa [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
  refine (Ideal.finite_factors hI).subset ?_
  intro w hw
  exact Ideal.dvd_span_singleton.mpr (mem_of_vAdd_ne w x hw)

theorem unzero_toAdd (m : ℤᵐ⁰) (h : m ≠ 0) : Multiplicative.toAdd (WithZero.unzero h) = WithZero.log m := by
  obtain ⟨a, rfl⟩ := WithZero.ne_zero_iff_exists.mp h
  first
  | rfl
  | simp [WithZero.log]
  | simp

theorem norm_embedding_eq {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (x : K) (hx : x ≠ 0) :
    ‖FinitePlace.embedding v x‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ (-(vAdd v x)) := by
  have hv : v.valuation K x ≠ 0 := by simpa using hx
  have he : Valued.v (FinitePlace.embedding v x) = v.valuation K x := by
    first
    | exact v.valuedAdicCompletion_eq_valuation' x
    | exact v.valuedAdicCompletion_eq_valuation x
    | rfl
  rw [FinitePlace.norm_def, he, WithZeroMulInt.toNNReal_neg_apply _ hv, unzero_toAdd _ hv]
  simp [vAdd]

theorem log_norm_embedding {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (x : K) (hx : x ≠ 0) :
    Real.log ‖FinitePlace.embedding v x‖ = -((vAdd v x : ℝ) * Real.log (Ideal.absNorm v.asIdeal : ℝ)) := by
  rw [norm_embedding_eq v x hx, Real.log_zpow]
  push_cast
  ring

theorem finsum_eq_log_norm {K : Type} [Field K] [NumberField K] (x : 𝓞 K) (hx : x ≠ 0) :
    ∑ᶠ w : HeightOneSpectrum (𝓞 K), lw K w * (vAdd w (algebraMap (𝓞 K) K x) : ℝ) =
      Real.log |((Algebra.norm ℤ x : ℤ) : ℝ)| / (Module.finrank ℚ K : ℝ) := by
  classical
  have hxK : algebraMap (𝓞 K) K x ≠ 0 := by
    first
    | simpa using hx
    | exact (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 K) K)).mpr hx
  have hf : ∀ w : HeightOneSpectrum (𝓞 K), lw K w * (vAdd w (algebraMap (𝓞 K) K x) : ℝ) =
      -Real.log ‖FinitePlace.embedding w (algebraMap (𝓞 K) K x)‖ / (Module.finrank ℚ K : ℝ) := by
    intro w
    rw [log_norm_embedding w _ hxK]
    unfold lw
    ring
  have hfin := volume_finite' K x hx
  have hsub : ∀ w, w ∉ hfin.toFinset → ‖FinitePlace.embedding w (algebraMap (𝓞 K) K x)‖ = 1 := by
    intro w hw
    have h0 : vAdd w (algebraMap (𝓞 K) K x) = 0 := by
      rw [Set.Finite.mem_toFinset, Function.mem_support, not_not] at hw
      exact hw
    rw [norm_embedding_eq w _ hxK, h0, neg_zero, zpow_zero]
  have hne : ∀ w ∈ hfin.toFinset, ‖FinitePlace.embedding w (algebraMap (𝓞 K) K x)‖ ≠ 0 :=
    fun w _ => norm_ne_zero_iff.mpr ((map_ne_zero _).mpr hxK)
  have hprod : ∏ᶠ w : HeightOneSpectrum (𝓞 K), ‖FinitePlace.embedding w (algebraMap (𝓞 K) K x)‖ =
      ∏ w ∈ hfin.toFinset, ‖FinitePlace.embedding w (algebraMap (𝓞 K) K x)‖ := by
    refine finprod_eq_prod_of_mulSupport_subset _ ?_
    intro w hw
    rw [Finset.mem_coe]
    by_contra hws
    exact hw (hsub w hws)
  have PF : ∏ᶠ w : FinitePlace K, w (algebraMap (𝓞 K) K x) = (|((Algebra.norm ℤ x : ℤ) : ℝ)|)⁻¹ := by
    have h := FinitePlace.prod_eq_inv_abs_norm_int hx
    first
    | exact h
    | (rw [Int.cast_abs] at h; exact h)
    | (push_cast at h; exact h)
    | (convert h using 3; simp)
  have PF' : ∏ᶠ w : HeightOneSpectrum (𝓞 K), ‖FinitePlace.embedding w (algebraMap (𝓞 K) K x)‖ =
      (|((Algebra.norm ℤ x : ℤ) : ℝ)|)⁻¹ := by
    rw [← PF]
    first
    | exact finprod_comp_equiv (FinitePlace.equivHeightOneSpectrum (K := K)).symm
    | exact finprod_eq_of_bijective (FinitePlace.equivHeightOneSpectrum (K := K)).symm (Equiv.bijective _)
        (fun _ => rfl)
    | exact (finprod_eq_of_bijective (FinitePlace.equivHeightOneSpectrum (K := K)).symm (Equiv.bijective _)
        (fun _ => rfl)).symm
  rw [finsum_congr hf, finsum_eq_sum_of_support_subset _ (s := hfin.toFinset) ?_]
  · rw [← Finset.sum_div, Finset.sum_neg_distrib,
      ← Real.log_prod hne,
      ← hprod, PF', Real.log_inv, neg_neg]
  · intro w hw
    rw [Finset.mem_coe]
    by_contra hws
    apply hw
    show -Real.log ‖FinitePlace.embedding w (algebraMap (𝓞 K) K x)‖ / (Module.finrank ℚ K : ℝ) = 0
    rw [hsub w hws, Real.log_one, neg_zero, zero_div]

theorem abs_norm_le {K : Type} [Field K] [NumberField K] (x : 𝓞 K) (B : ℝ) (hB : 0 ≤ B)
    (hσ : ∀ σ : K →+* ℂ, ‖σ (algebraMap (𝓞 K) K x)‖ ≤ B) :
    |((Algebra.norm ℤ x : ℤ) : ℝ)| ≤ B ^ Module.finrank ℚ K := by
  have h1 : |((Algebra.norm ℤ x : ℤ) : ℝ)| =
      ∏ w : InfinitePlace K, w (algebraMap (𝓞 K) K x) ^ w.mult := by
    rw [InfinitePlace.prod_eq_abs_norm, ← Algebra.coe_norm_int]
    first
    | simp
    | norm_cast
  rw [h1, ← InfinitePlace.sum_mult_eq, ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_le_prod (fun w _ => pow_nonneg (AbsoluteValue.nonneg _ _) _) (fun w _ => ?_)
  refine pow_le_pow_left₀ (AbsoluteValue.nonneg _ _) ?_ _
  rw [← InfinitePlace.norm_embedding_eq]
  exact hσ _

theorem volume_sum_le : VSumLe := by
  intro K _ _ x B hx hB hσ
  rw [finsum_eq_log_norm x hx]
  have hd : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
  have hN : (0 : ℝ) < |((Algebra.norm ℤ x : ℤ) : ℝ)| := by
    rw [abs_pos, Int.cast_ne_zero, Ne, Algebra.norm_eq_zero_iff]
    exact hx
  rw [div_le_iff₀ hd, mul_comm, ← Real.log_pow]
  exact Real.log_le_log hN (abs_norm_le x B hB.le hσ)

end PI.Dv.TIW
