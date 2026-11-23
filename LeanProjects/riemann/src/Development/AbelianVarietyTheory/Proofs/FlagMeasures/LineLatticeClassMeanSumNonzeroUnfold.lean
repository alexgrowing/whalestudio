import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsLatMeasurableConst
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LineLatticeMeanSumEqTsumPairOrbitsStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LineLatticeMeanSinglePairOrbitContributionStatement

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase

namespace GlobalTheory.FlagBase.SiegelUnfold

open Filter Topology in

theorem lseriesSummable_idealCount (K : Type) [Field K] [NumberField K] {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n => ((Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℝ) : ℂ)) s := by
  refine LSeriesSummable_of_sum_norm_bigO_and_nonneg (r := 1) ?_ (fun _ => Nat.cast_nonneg _)
    zero_le_one hs
  have h : Tendsto (fun n : ℕ => (∑ k ∈ Finset.Icc 1 n,
      (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = k} : ℝ)) / (n : ℝ)) atTop
      (𝓝 (dedekindZeta_residue K)) := by
    refine ((Ideal.tendsto_norm_le_div_atTop₀ K).comp tendsto_natCast_atTop_atTop).congr fun n ↦ ?_
    simp only [Function.comp_apply, Nat.cast_le, ← Nat.cast_sum]
    congr
    rw [← add_left_inj 1, ← Ideal.card_norm_le_eq_card_norm_le_add_one,
      show Finset.Icc 1 n = Finset.Ioc 0 n from Finset.Icc_succ_left_eq_Ioc _ _,
      show 1 = Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = 0} by simp [Ideal.absNorm_eq_zero_iff],
      Finset.sum_Ioc_add_eq_sum_Icc (n.zero_le),
      ← Finset.card_preimage_eq_sum_card_image_eq (fun k _ ↦ Ideal.finite_setOfPred_absNorm_eq k)]
    simp [Set.coe_eq_subtype]
  simp only [Real.rpow_one]
  exact Asymptotics.isBigO_of_div_tendsto_nhds (by
    filter_upwards [eventually_gt_atTop 0] with n hn h0
    exact absurd (Nat.cast_eq_zero.1 h0) hn.ne') _ h

theorem hasSum_zetaE (K : Type) [Field K] [NumberField K] {l : ℕ} (hl : 2 ≤ l) :
    HasSum (fun n : ℕ => (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℝ) * ((n : ℝ) ^ l)⁻¹)
      (zetaE K l) := by
  have hs : 1 < ((l : ℂ)).re := by
    rw [Complex.natCast_re]; exact_mod_cast hl
  have h := Complex.hasSum_re (lseriesSummable_idealCount K hs).hasSum
  unfold zetaE dedekindZeta LSeries
  simp only [Complex.ofReal_natCast] at h
  convert h using 2 with n
  rcases eq_or_ne n 0 with rfl | hn
  · have : l ≠ 0 := by omega
    simp [this]
  · rw [LSeries.term_of_ne_zero hn, Complex.cpow_natCast, div_eq_mul_inv, ← Complex.ofReal_natCast,
      ← Complex.ofReal_natCast n, ← Complex.ofReal_pow, ← Complex.ofReal_inv, ← Complex.ofReal_mul,
      Complex.ofReal_re]

theorem tsum_absNorm_pow_inv (K : Type) [Field K] [NumberField K] {l : ℕ} (hl : 2 ≤ l) :
    ∑' 𝔞 : {𝔞 : Ideal (𝓞 K) // 𝔞 ≠ ⊥}, ENNReal.ofReal (((Ideal.absNorm 𝔞.1 : ℝ) ^ l)⁻¹) =
      ENNReal.ofReal (zetaE K l) := by
  have hl0 : l ≠ 0 := by omega
  have h1 : ∑' 𝔞 : {𝔞 : Ideal (𝓞 K) // 𝔞 ≠ ⊥}, ENNReal.ofReal (((Ideal.absNorm 𝔞.1 : ℝ) ^ l)⁻¹) =
      ∑' 𝔞 : Ideal (𝓞 K), ENNReal.ofReal (((Ideal.absNorm 𝔞 : ℝ) ^ l)⁻¹) := by
    refine tsum_subtype_eq_of_support_subset (s := {𝔞 : Ideal (𝓞 K) | 𝔞 ≠ ⊥})
      (f := fun 𝔞 : Ideal (𝓞 K) => ENNReal.ofReal (((Ideal.absNorm 𝔞 : ℝ) ^ l)⁻¹)) ?_
    rintro 𝔞 h rfl
    exact h (by simp [hl0])
  have h := hasSum_zetaE K hl
  rw [h1, ← h.tsum_eq, ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) h.summable,
    ← (Equiv.sigmaFiberEquiv (fun I : Ideal (𝓞 K) => Ideal.absNorm I)).tsum_eq, ENNReal.tsum_sigma']
  refine tsum_congr fun n => ?_
  have key : ∀ I : {I : Ideal (𝓞 K) // Ideal.absNorm I = n},
      ENNReal.ofReal (((Ideal.absNorm
        (Equiv.sigmaFiberEquiv (fun I : Ideal (𝓞 K) => Ideal.absNorm I) ⟨n, I⟩) : ℝ) ^ l)⁻¹) =
      ENNReal.ofReal (((n : ℝ) ^ l)⁻¹) := by
    rintro ⟨I, rfl⟩; rfl
  haveI : Finite {I : Ideal (𝓞 K) // Ideal.absNorm I = n} :=
    (Ideal.finite_setOfPred_absNorm_eq n).to_subtype
  haveI := Fintype.ofFinite {I : Ideal (𝓞 K) // Ideal.absNorm I = n}
  rw [tsum_congr key, tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast, Nat.card_eq_fintype_card]

def sumLat (E : Type) [Field E] [NumberField E] (k : ℕ) (𝔞 : Ideal (𝓞 E))
    (Λ' : Submodule (𝓞 E) (Fin k → E)) : Submodule (𝓞 E) (Fin (k + 1) → E) where
  carrier := {y | (∀ t ∈ 𝔞, (t : E) * y 0 ∈ (algebraMap (𝓞 E) E).range) ∧ Fin.tail y ∈ Λ'}
  add_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨fun t ht => ?_, Λ'.add_mem ha' hb'⟩
    rw [Pi.add_apply, mul_add]
    exact add_mem (ha t ht) (hb t ht)
  zero_mem' := ⟨fun t _ => by simp, Λ'.zero_mem⟩
  smul_mem' := by
    rintro c a ⟨ha, ha'⟩
    refine ⟨fun t ht => ?_, Λ'.smul_mem c ha'⟩
    have := ha (t * c) (𝔞.mul_mem_right c ht)
    simpa [Algebra.smul_def, mul_assoc] using this

theorem latMean_sum_ne_zero : ∀ (E : Type) [Field E] [NumberField E], IsTotallyComplex E → ∀ j : ℕ, 2 ≤ j → ∀ (w : ℝ → ENNReal) (Φ : VecInf E j → ENNReal), Measurable w → Measurable Φ → latMean E j (fun L => w (covAt E j L) * ∑' x : {x : VecInf E j // x ∈ L ∧ x ≠ 0}, Φ x.1) = glVol E (j - 1) * ENNReal.ofReal (Formalism.HermitianLatticesTheory.vInv E ^ (Formalism.HermitianLatticesTheory.fDeg E * (2 * j - 1)) * zetaE E j) * (∫⁻ x, Φ x) * ∫⁻ t in Set.Ioi (0 : ℝ), w t / ENNReal.ofReal (t ^ 2) := by
  intro E _ _ hE j hj w Φ hw hΦ
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  have hv : 0 ≤ Formalism.HermitianLatticesTheory.vInv E ^ (Formalism.HermitianLatticesTheory.fDeg E * (2 * k + 1)) := by
    unfold Formalism.HermitianLatticesTheory.vInv; positivity
  rw [GlobalTheory.T.lineLatticeMean_sum_eq_tsum_pair_orbits E hE k (sumLat E k) (fun _ _ _ => Iff.rfl) w Φ hw hΦ]
  simp only [fun (𝔞 : {𝔞 : Ideal (𝓞 E) // 𝔞 ≠ ⊥})
      (Λ' : {Λ : Submodule (𝓞 E) (Fin k → E) // Submodule.IsLattice E Λ}) =>
    GlobalTheory.T.lineLatticeMean_single_pair_orbit_contribution E hE k (by omega) (sumLat E k) (fun _ _ _ => Iff.rfl) w Φ hw hΦ 𝔞.1 Λ'.1 𝔞.2 Λ'.2]
  simp only [ENNReal.tsum_mul_right, ENNReal.tsum_mul_left, ENNReal.ofReal_mul hv,
    Nat.add_sub_cancel, show 2 * (k + 1) - 1 = 2 * k + 1 by omega]
  rw [tsum_absNorm_pow_inv E hj]
  rfl

end GlobalTheory.FlagBase.SiegelUnfold
