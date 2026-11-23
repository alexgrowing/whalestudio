import Mathlib
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Arith.Iwasawa

open PowerSeries IsLocalRing
open scoped Polynomial

variable (p : ℕ) [hp : Fact p.Prime]

abbrev Lambda : Type := PowerSeries ℤ_[p]

theorem isDomain : IsDomain (Lambda p) := inferInstance

theorem isLocalRing : IsLocalRing (Lambda p) := inferInstance

theorem isNoetherianRing : IsNoetherianRing (Lambda p) := inferInstance

theorem padic_p_not_isUnit : ¬ IsUnit (p : ℤ_[p]) := by
  have hmem : (p : ℤ_[p]) ∈ maximalIdeal ℤ_[p] := by
    rw [PadicInt.maximalIdeal_eq_span_p]; exact Ideal.subset_span rfl
  exact (mem_maximalIdeal _).1 hmem

theorem p_not_isUnit : ¬ IsUnit (C (p : ℤ_[p]) : Lambda p) := by
  rw [isUnit_iff_constantCoeff, constantCoeff_C]
  exact padic_p_not_isUnit p

theorem X_not_isUnit : ¬ IsUnit (X : Lambda p) := by
  rw [isUnit_iff_constantCoeff, constantCoeff_X]
  exact not_isUnit_zero

theorem maximalIdeal_eq_span :
    maximalIdeal (Lambda p) = Ideal.span {C (p : ℤ_[p]), X} := by
  apply le_antisymm
  · intro f hf
    rw [mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_constantCoeff] at hf
    have h0 : constantCoeff f ∈ maximalIdeal ℤ_[p] := hf
    rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at h0
    obtain ⟨a, ha⟩ := h0
    rw [eq_X_mul_shift_add_const f, ha, map_mul]
    refine Ideal.add_mem _ (Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp)))
      (Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp)))
  · rw [Ideal.span_le]
    rintro x (rfl | rfl)
    · exact (mem_maximalIdeal _).2 (p_not_isUnit p)
    · exact (mem_maximalIdeal _).2 (X_not_isUnit p)

theorem spanFinrank_maximalIdeal_le_two : (maximalIdeal (Lambda p)).spanFinrank ≤ 2 := by
  rw [maximalIdeal_eq_span]
  refine (Submodule.spanFinrank_span_le_ncard_of_finite (Set.toFinite _)).trans ?_
  exact (Set.ncard_insert_le _ _).trans (by simp)

theorem ringKrullDim_eq_two : ringKrullDim (Lambda p) = 2 := by
  apply le_antisymm
  · refine (ringKrullDim_le_spanFinrank_maximalIdeal (Lambda p)).trans ?_
    exact_mod_cast spanFinrank_maximalIdeal_le_two p
  · have h1 : ringKrullDim ℤ_[p] = 1 := IsDiscreteValuationRing.ringKrullDim_eq_one ℤ_[p]
    have h2 := ringKrullDim_succ_le_ringKrullDim_powerseries (R := ℤ_[p])
    rw [h1] at h2
    exact le_of_eq_of_le (by rfl) h2

instance isRegularLocalRing : IsRegularLocalRing (Lambda p) :=
  IsRegularLocalRing.of_spanFinrank_maximalIdeal_le _ (by
    rw [ringKrullDim_eq_two]; exact_mod_cast spanFinrank_maximalIdeal_le_two p)

def IsDistinguished (P : ℤ_[p][X]) : Prop :=
  P.IsDistinguishedAt (maximalIdeal ℤ_[p])

variable {p}

theorem IsDistinguished.monic {P : ℤ_[p][X]} (hP : IsDistinguished p P) : P.Monic :=
  Polynomial.IsDistinguishedAt.monic hP

theorem IsDistinguished.mul {P Q : ℤ_[p][X]} (hP : IsDistinguished p P)
    (hQ : IsDistinguished p Q) : IsDistinguished p (P * Q) :=
  Polynomial.IsDistinguishedAt.mul hP hQ

theorem IsDistinguished.ne_zero {P : ℤ_[p][X]} (hP : IsDistinguished p P) : P ≠ 0 :=
  hP.monic.ne_zero

theorem IsDistinguished.map_mk {P : ℤ_[p][X]} (hP : IsDistinguished p P) :
    (P : Lambda p).map (Ideal.Quotient.mk (maximalIdeal ℤ_[p])) = X ^ P.natDegree := by
  rw [← Polynomial.polynomial_map_coe, Polynomial.IsDistinguishedAt.map_eq_X_pow hP,
    Polynomial.coe_pow, Polynomial.coe_X]

end GroundTheory.Arith.Iwasawa
