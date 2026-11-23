import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.U2ringPfDMain

noncomputable section

open Classical

namespace Formalism.MainNotions.N.Ln34

section U2E

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O]
  [IsAdicComplete (IsLocalRing.maximalIdeal O) O]

local notation "mkI" y => Ideal.Quotient.mk (DualFramesAlt.eigenRingInvariants.Ia y)

theorem u2ringPfE_mem_max (p : ℕ) [hp : Fact p.Prime] (hpm : (p : O) ∈ IsLocalRing.maximalIdeal O)
    {x : O} (hroot : (1 + x) ^ p = 1) : x ∈ IsLocalRing.maximalIdeal O := by
  have : CharP (IsLocalRing.ResidueField O) p :=
    (CharP.charP_iff_prime_eq_zero hp.out).mpr (by
      rw [← map_natCast (IsLocalRing.residue O), IsLocalRing.residue_eq_zero_iff]; exact hpm)
  have h := congrArg (IsLocalRing.residue O) hroot
  rw [map_pow, map_add, map_one, add_pow_char, one_pow] at h
  have h2 : (IsLocalRing.residue O x) ^ p = 0 := by linear_combination h
  have h3 := (pow_eq_zero_iff hp.out.ne_zero).mp h2
  rwa [IsLocalRing.residue_eq_zero_iff] at h3

theorem u2ringPfE_val_unit {y c : O} (hy : y ∈ IsLocalRing.maximalIdeal O) {F : PowerSeries O}
    (hF : IsUnit (PowerSeries.constantCoeff F)) (hc : (mkI y) F = (mkI y) (PowerSeries.C c)) :
    IsUnit c := by
  obtain ⟨H, hH⟩ := DualFramesAlt.BlockProductRing.dvd_of_mk_eq hc
  have h0 := congrArg PowerSeries.constantCoeff hH
  simp only [map_sub, map_mul, PowerSeries.constantCoeff_X, PowerSeries.constantCoeff_C, zero_sub] at h0
  by_contra hnu
  have hcm : c ∈ IsLocalRing.maximalIdeal O := (IsLocalRing.mem_maximalIdeal _).2 (mem_nonunits_iff.2 hnu)
  have hFm : PowerSeries.constantCoeff F ∈ IsLocalRing.maximalIdeal O := by
    have e0 : PowerSeries.constantCoeff F = c + -y * PowerSeries.constantCoeff H := by linear_combination h0
    rw [e0]
    exact Ideal.add_mem _ hcm (Ideal.mul_mem_right _ _ ((Ideal.neg_mem_iff _).2 hy))
  exact (mem_nonunits_iff.1 ((IsLocalRing.mem_maximalIdeal _).1 hFm)) hF

theorem u2ringPfE_mk_aeval {x y : O} {P : PowerSeries O} (hP : (mkI x) P = (mkI x) (PowerSeries.C y))
    (E : Polynomial O) :
    (mkI x) (Polynomial.aeval P E) = (mkI x) (PowerSeries.C (E.eval y)) := by
  have h1 : (mkI x) (Polynomial.aeval P E) =
      Polynomial.aeval ((mkI x) P) E := by
    rw [← Ideal.Quotient.mkₐ_eq_mk O, Polynomial.aeval_algHom_apply]
  rw [h1, hP, ← Ideal.Quotient.mkₐ_eq_mk O, Polynomial.aeval_algHom_apply]
  congr 1
  show Polynomial.aeval (PowerSeries.C y) E = PowerSeries.C (E.eval y)
  rw [show (PowerSeries.C y : PowerSeries O) = algebraMap O (PowerSeries O) y by
    rw [PowerSeries.algebraMap_apply]; rfl, Polynomial.aeval_algebraMap_apply]
  rw [PowerSeries.algebraMap_apply]; rfl

end U2E

end Formalism.MainNotions.N.Ln34
