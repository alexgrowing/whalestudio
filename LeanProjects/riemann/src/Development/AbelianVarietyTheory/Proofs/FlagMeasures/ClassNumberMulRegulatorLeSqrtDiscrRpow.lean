import Mathlib
import Formalism.HermitianLattices.StatementMass
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RegulatorLeSumSmallIdealsInClassStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SumAbsNormRpowNegLeDedekindZetaBoundStatement
open MeasureTheory NumberField Finset

namespace GlobalTheory

theorem log_pow_div_factorial_le_rpow_of_one_le {u s : ℝ} (hu : 1 ≤ u) (hs : 1 ≤ s) (r : ℕ) :
    Real.log u ^ r / (r.factorial : ℝ) ≤ u ^ s := by
  have h := Real.pow_div_factorial_le_exp (Real.log u) (Real.log_nonneg hu) r
  rw [Real.exp_log (by linarith)] at h
  refine h.trans ?_
  calc u = u ^ (1 : ℝ) := (Real.rpow_one u).symm
    _ ≤ u ^ s := Real.rpow_le_rpow_of_exponent_le hu hs

theorem classNumber_mul_regulator_le_sqrt_discr_rpow :
    ∀ (K : Type) [Field K] [NumberField K], IsTotallyComplex K → ∀ s : ℝ, 1 < s →
      (classNumber K : ℝ) * Units.regulator K ≤
        Real.sqrt |(discr K : ℝ)| ^ s * (s / (s - 1)) ^ Module.finrank ℚ K := by
  intro K _ _ hK s hs
  classical
  set Y : ℝ := Real.sqrt |(discr K : ℝ)| with hY
  have hY0 : 0 ≤ Y := Real.sqrt_nonneg _
  have hfin : {I : Ideal (𝓞 K) | I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ Y}.Finite := by
    refine (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 K) ⌊Y⌋₊).subset fun I hI => ?_
    exact Nat.le_floor hI.2
  set T := hfin.toFinset with hT
  have hmem : ∀ I, I ∈ T ↔ I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ Y := fun I => by
    rw [hT, Set.Finite.mem_toFinset]; rfl
  let cls : Ideal (𝓞 K) → ClassGroup (𝓞 K) := fun I =>
    if h : I ∈ nonZeroDivisors (Ideal (𝓞 K)) then ClassGroup.mk0 ⟨I, h⟩ else 1
  let g : Ideal (𝓞 K) → ℝ := fun I =>
    Real.log (Y / Ideal.absNorm I) ^ Units.rank K / ((Units.rank K).factorial : ℝ)
  have h1 : ∀ C : ClassGroup (𝓞 K),
      Units.regulator K ≤ ∑ I ∈ T.filter (fun I => cls I = C), g I := by
    intro C
    refine GlobalTheory.T.regulator_le_sum_small_ideals_in_class K hK C _ fun I => ?_
    rw [Finset.mem_filter, hmem]
    constructor
    · rintro ⟨⟨h0, hle⟩, hc⟩
      have hI : I ∈ nonZeroDivisors (Ideal (𝓞 K)) := mem_nonZeroDivisors_of_ne_zero h0
      refine ⟨hI, ?_, hle⟩
      simpa only [cls, dif_pos hI] using hc
    · rintro ⟨hI, hc, hle⟩
      refine ⟨⟨nonZeroDivisors.ne_zero hI, hle⟩, ?_⟩
      simpa only [cls, dif_pos hI] using hc
  have h2 : ∀ I ∈ T, g I ≤ Y ^ s * (Ideal.absNorm I : ℝ) ^ (-s) := by
    intro I hI
    obtain ⟨h0, hle⟩ := (hmem I).1 hI
    have hN : (0 : ℝ) < Ideal.absNorm I := by
      have : Ideal.absNorm I ≠ 0 := fun h => h0 (Ideal.absNorm_eq_zero_iff.1 h)
      exact_mod_cast Nat.pos_of_ne_zero this
    have hu : 1 ≤ Y / Ideal.absNorm I := (one_le_div hN).2 hle
    refine (log_pow_div_factorial_le_rpow_of_one_le hu hs.le _).trans (le_of_eq ?_)
    rw [Real.div_rpow hY0 hN.le, Real.rpow_neg hN.le, div_eq_mul_inv]
  calc (classNumber K : ℝ) * Units.regulator K
      = ∑ _C : ClassGroup (𝓞 K), Units.regulator K := by
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, classNumber]
    _ ≤ ∑ C : ClassGroup (𝓞 K), ∑ I ∈ T.filter (fun I => cls I = C), g I :=
        Finset.sum_le_sum fun C _ => h1 C
    _ = ∑ I ∈ T, g I := Finset.sum_fiberwise T cls g
    _ ≤ ∑ I ∈ T, Y ^ s * (Ideal.absNorm I : ℝ) ^ (-s) := Finset.sum_le_sum h2
    _ = Y ^ s * ∑ I ∈ T, (Ideal.absNorm I : ℝ) ^ (-s) := (Finset.mul_sum _ _ _).symm
    _ ≤ Y ^ s * (s / (s - 1)) ^ Module.finrank ℚ K :=
        mul_le_mul_of_nonneg_left
          (GlobalTheory.T.sum_absNorm_rpow_neg_le_dedekindZeta_bound K s hs T fun I hI => ((hmem I).1 hI).1) (Real.rpow_nonneg hY0 s)

end GlobalTheory
