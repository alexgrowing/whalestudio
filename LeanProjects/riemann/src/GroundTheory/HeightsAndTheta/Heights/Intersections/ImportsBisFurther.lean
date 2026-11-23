import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsMoreAlt
import GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsBisAlt
import GroundTheory.HeightsAndTheta.Heights.Intersections.LeOfHeightMapEqZero
import GroundTheory.HeightsAndTheta.Heights.Intersections.PLocRingPow
import GroundTheory.HeightsAndTheta.Heights.Intersections.LogCardLocIdealUnitMul
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

theorem RegularityLocalPrime.proof (h₁ : RegularityOrder.Statement) : RegularityLocalPrime.Statement := by
  intro K _ ι _ P p y hP hp hy
  have hPp : P.IsPrime := hP.2.1.1
  obtain ⟨c, hc0, hc⟩ := RegularityDenominator.proof RegularityDivisorSupportClosed.proof LocRingPow.proof K ι P y hP
  have hcR : c ∈ regRing P := fun W h1 h2 => (hc W h1 h2).1
  have : Module.Finite ℤ (regRing P) := (h₁ K ι P hP).2.1
  have hci : IsIntegral ℤ (⟨c, hcR⟩ : regRing P) := Algebra.IsIntegral.isIntegral _
  have hne := Ideal.comap_ne_bot_of_integral_mem (I := Ideal.span {(⟨c, hcR⟩ : regRing P)})
    (fun h => hc0 (congrArg Subtype.val h)) (Ideal.mem_span_singleton_self _) hci
  obtain ⟨N, hN, hN0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.1 (Ideal.mem_comap.1 hN)
  have hNF : ((N : funField P) : FractionRing (MRing ι ⧸ P)) =
      ((d : funField P) : FractionRing (MRing ι ⧸ P)) * (c : FractionRing (MRing ι ⧸ P)) := by
    have h := congrArg (fun z : regRing P => ((z : funField P) : FractionRing (MRing ι ⧸ P))) hd
    simp only [Subring.coe_mul, algebraMap_int_eq, eq_intCast, SubringClass.coe_intCast] at h
    simp only [SubringClass.coe_intCast]
    exact h.symm
  have hpu : p.natAbs ≠ 1 := fun h => hp.not_isUnit (Int.isUnit_iff_natAbs_eq.mpr h)
  obtain ⟨m, hNm, hpm⟩ := (Int.finiteMultiplicity_iff.mpr ⟨hpu, hN0⟩).exists_eq_pow_mul_and_not_dvd
  generalize multiplicity p N = e at hNm
  refine ⟨m, hpm, fun W h1 h2 => ?_⟩
  rw [Subring.coe_mul, SubringClass.coe_intCast]
  by_cases hpW : C p ∈ W
  · exact mul_mem (intCast_mem _ m) (hy W h1 h2 hpW)
  have hCp : algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P (C p)) = (p : _) := by
    rw [eq_intCast C p, map_intCast, map_intCast]
  have hp0 : (p : FractionRing (MRing ι ⧸ P)) ≠ 0 := by
    intro h
    apply hpW
    apply h2
    rw [← Ideal.Quotient.eq_zero_iff_mem, ← IsFractionRing.to_map_eq_zero_iff (K := FractionRing (MRing ι ⧸ P)),
      hCp, h]
  have hq : (p : FractionRing (MRing ι ⧸ P))⁻¹ ∈ locRing P W :=
    frac_mem_locRing h2 (RegularityDenominator.isMultiHomog_C 1) (RegularityDenominator.isMultiHomog_C p) hpW
      (by rw [hCp, map_one, map_one, map_one, inv_mul_cancel₀ hp0])
  have hyc : (y : FractionRing (MRing ι ⧸ P)) * (c : FractionRing (MRing ι ⧸ P)) ∈ locRing P W := by
    have := (hc W h1 h2).2
    rwa [Subring.coe_mul] at this
  have hdW : ((d : funField P) : FractionRing (MRing ι ⧸ P)) ∈ locRing P W := d.2 W h1 h2
  have key : (m : FractionRing (MRing ι ⧸ P)) * (y : FractionRing (MRing ι ⧸ P)) =
      (p : FractionRing (MRing ι ⧸ P))⁻¹ ^ e *
        (((d : funField P) : FractionRing (MRing ι ⧸ P)) * ((y : FractionRing (MRing ι ⧸ P)) * c)) := by
    have hN' : ((d : funField P) : FractionRing (MRing ι ⧸ P)) * ((y : FractionRing (MRing ι ⧸ P)) * c) =
        (p : FractionRing (MRing ι ⧸ P)) ^ e * m * y := by
      rw [show ((d : funField P) : FractionRing (MRing ι ⧸ P)) * ((y : FractionRing (MRing ι ⧸ P)) * c) =
        ((N : funField P) : FractionRing (MRing ι ⧸ P)) * y by rw [hNF]; ring, SubringClass.coe_intCast,
        hNm, Int.cast_mul, Int.cast_pow]
    rw [hN', inv_pow, ← mul_assoc, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hp0), one_mul]
  rw [key]
  exact mul_mem (pow_mem hq _) (mul_mem hdW hyc)

end

end GroundTheory.Heights₂.Heights.Inter
