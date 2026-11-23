import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HarishChandraFormulaStatement

noncomputable section

open Polynomial

namespace CrystallineSemistableComparison

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

theorem mem_OK (x : K) : x ∈ OK l K ↔ ‖(x : PadicAlgCl l)‖ ≤ 1 := by
  show (x : PadicAlgCl l) ∈ GroundTheory.PAdicHodge.normInteger (PadicAlgCl l) ↔ _
  exact GroundTheory.PAdicHodge.mem_normInteger

theorem isIntegral_iff_norm_le (x : PadicAlgCl l) : IsIntegral ℤ_[l] x ↔ ‖x‖ ≤ 1 := by
  have hi : IsIntegral ℚ_[l] x := Algebra.IsIntegral.isIntegral x
  show _ ↔ spectralValue (minpoly ℚ_[l] x) ≤ 1
  rw [spectralValue_le_one_iff (minpoly.monic hi)]
  constructor
  · intro h n
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] h, coeff_map]
    exact PadicInt.norm_le_one _
  · intro h
    have hl' : minpoly ℚ_[l] x ∈ lifts (algebraMap ℤ_[l] ℚ_[l]) :=
      (lifts_iff_coeff_lifts _).mpr fun n => ⟨⟨_, h n⟩, rfl⟩
    obtain ⟨q, hq, -, hqm⟩ := lifts_and_degree_eq_and_monic hl' (minpoly.monic hi)
    exact ⟨q, hqm, by rw [← aeval_def, ← aeval_map_algebraMap ℚ_[l], hq, minpoly.aeval]⟩

theorem OK_eq : OK l K = (integralClosure ℤ_[l] K).toSubring := by
  ext x
  rw [mem_OK, ← isIntegral_iff_norm_le]
  show _ ↔ IsIntegral ℤ_[l] x
  exact (isIntegral_algHom_iff (K.val.restrictScalars ℤ_[l]) Subtype.val_injective)

theorem norm_OK_le (a : OK l K) : ‖((a : K) : PadicAlgCl l)‖ ≤ 1 := (mem_OK _).1 a.2

theorem isUnit_OK_iff (a : OK l K) : IsUnit a ↔ ‖((a : K) : PadicAlgCl l)‖ = 1 := by
  constructor
  · rintro ⟨u, rfl⟩
    have h1 := norm_OK_le (u : OK l K)
    have h2 := norm_OK_le ((u⁻¹ : (OK l K)ˣ) : OK l K)
    have h3 : ((((u : OK l K) : K) : PadicAlgCl l)) * (((((u⁻¹ : (OK l K)ˣ) : OK l K) : K) : PadicAlgCl l)) = 1 := by
      have := congrArg (fun z : OK l K => ((z : K) : PadicAlgCl l)) u.mul_inv
      exact this
    have h4 := congrArg norm h3
    rw [norm_mul, norm_one] at h4
    refine le_antisymm h1 ?_
    calc (1 : ℝ) = _ := h4.symm
      _ ≤ _ := mul_le_of_le_one_right (norm_nonneg _) h2
  · intro h
    have ha : (a : K) ≠ 0 := by
      intro e; rw [e] at h; simp at h
    refine isUnit_iff_exists_inv.2 ⟨⟨(a : K)⁻¹, (mem_OK _).2 ?_⟩, Subtype.ext ?_⟩
    · rw [IntermediateField.coe_inv, norm_inv, h, inv_one]
    · show (a : K) * (a : K)⁻¹ = 1
      exact mul_inv_cancel₀ ha

theorem norm_lt_one_of_irreducible {ϖ : OK l K} (h : Irreducible ϖ) : ‖((ϖ : K) : PadicAlgCl l)‖ < 1 :=
  lt_of_le_of_ne (norm_OK_le ϖ) fun e => h.not_isUnit ((isUnit_OK_iff ϖ).2 e)

theorem ne_zero_of_irreducible {ϖ : OK l K} (h : Irreducible ϖ) : ((ϖ : K) : PadicAlgCl l) ≠ 0 := by
  intro e
  apply h.ne_zero
  exact Subtype.ext (Subtype.ext e)

theorem OK_away {ϖ : OK l K} (h : Irreducible ϖ) : IsLocalization.Away ϖ K := by
  have h0 := ne_zero_of_irreducible h
  have h1 := norm_lt_one_of_irreducible h
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨_, n, rfl⟩
    refine IsUnit.mk0 _ ?_
    show ((ϖ ^ n : OK l K) : K) ≠ 0
    intro e
    apply h0
    have : ((ϖ : K) : PadicAlgCl l) ^ n = 0 := by
      have := congrArg (fun z : K => (z : PadicAlgCl l)) e
      simpa using this
    exact pow_eq_zero_iff'.1 this |>.1
  · intro z
    by_cases hz : z = 0
    · exact ⟨⟨0, 1⟩, by simp [hz]⟩
    have hz' : 0 < ‖(z : PadicAlgCl l)‖ := norm_pos_iff.2 (by exact_mod_cast hz)
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (inv_pos.2 hz') h1
    refine ⟨⟨⟨z * (ϖ : K) ^ n, (mem_OK _).2 ?_⟩, ⟨ϖ ^ n, n, rfl⟩⟩, ?_⟩
    · show ‖((z * (ϖ : K) ^ n : K) : PadicAlgCl l)‖ ≤ 1
      rw [IntermediateField.coe_mul, IntermediateField.coe_pow, norm_mul, norm_pow]
      have := mul_lt_mul_of_pos_left hn hz'
      rw [mul_inv_cancel₀ hz'.ne'] at this
      exact this.le
    · rfl
  · intro x y e
    exact ⟨1, by simpa using Subtype.ext e⟩

variable [FiniteDimensional ℚ_[l] K]

instance : IsLocalRing (OK l K) := .of_nonunits_add fun a b ha hb => by
  rw [mem_nonunits_iff, isUnit_OK_iff] at *
  have h1 := lt_of_le_of_ne (norm_OK_le a) ha
  have h2 := lt_of_le_of_ne (norm_OK_le b) hb
  show ‖((a : K) : PadicAlgCl l) + ((b : K) : PadicAlgCl l)‖ ≠ 1
  exact ((PadicAlgCl.isNonarchimedean l _ _).trans_lt (max_lt h1 h2)).ne

theorem OK_dvr : IsDiscreteValuationRing (OK l K) := by
  have hded : IsDedekindDomain (OK l K) := by
    rw [OK_eq]
    exact IsIntegralClosure.isDedekindDomain ℤ_[l] ℚ_[l] K (integralClosure ℤ_[l] K)
  have hlm : ((l : ℕ) : OK l K) ∈ IsLocalRing.maximalIdeal (OK l K) := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_OK_iff]
    have e : (((((l : ℕ) : OK l K) : K)) : PadicAlgCl l) = algebraMap ℚ_[l] (PadicAlgCl l) (l : ℚ_[l]) := by simp
    rw [e, PadicAlgCl.norm_extends]
    exact Padic.norm_p_lt_one.ne
  have hnf : ¬ IsField (OK l K) := fun hf => by
    rw [IsLocalRing.isField_iff_maximalIdeal_eq.mp hf, Ideal.mem_bot] at hlm
    exact (Fact.out : l.Prime).ne_zero (Nat.cast_injective (R := OK l K) (by simpa using hlm))
  exact ((IsDiscreteValuationRing.TFAE _ hnf).out 0 2).mpr hded

end CrystallineSemistableComparison
