import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniformBaseChange.MemRangeOfForallHeightOne

namespace GlobalTheory

theorem dvd_of_associated_at_height_one (A : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [IsIntegrallyClosed A] (a b : A) (hb : b ≠ 0)
    (h : ∀ (q : Ideal A) [q.IsPrime], q.height = 1 →
      Associated (algebraMap A (Localization.AtPrime q) a)
        (algebraMap A (Localization.AtPrime q) b)) : b ∣ a := by
  let K := FractionRing A
  have hbK : algebraMap A K b ≠ 0 := fun h0 =>
    hb (IsFractionRing.injective A K (by rw [h0, map_zero]))
  have hmem : algebraMap A K a / algebraMap A K b ∈ (algebraMap A K).range := by
    refine ReciprocityTheory.ChartRestriction.G.Out.KrullAlg.mem_range_of_forall_height_one (A := A) _ ?_
    intro P hP h1
    obtain ⟨u, hu⟩ := h P h1
    obtain ⟨c, s, hcs⟩ := IsLocalization.exists_mk'_eq P.primeCompl
      (((u⁻¹ : (Localization.AtPrime P)ˣ)) : Localization.AtPrime P)
    have h2 : algebraMap A (Localization.AtPrime P) a =
        algebraMap A (Localization.AtPrime P) b * IsLocalization.mk' _ c s := by
      rw [hcs, ← hu, mul_assoc, Units.mul_inv, mul_one]
    have h3 : algebraMap A (Localization.AtPrime P) (a * s) =
        algebraMap A (Localization.AtPrime P) (b * c) := by
      rw [map_mul, h2, mul_assoc, IsLocalization.mk'_spec, map_mul]
    have e : a * s = b * c :=
      IsLocalization.injective (Localization.AtPrime P) P.primeCompl_le_nonZeroDivisors h3
    refine ⟨s, s.2, c, ?_⟩
    have e' : algebraMap A K a * algebraMap A K s = algebraMap A K b * algebraMap A K c := by
      rw [← map_mul, ← map_mul, e]
    rw [← mul_div_assoc, eq_div_iff hbK]
    linear_combination -e'
  obtain ⟨c, hc⟩ := hmem
  refine ⟨c, IsFractionRing.injective A K ?_⟩
  rw [map_mul, hc, mul_div_assoc', eq_div_iff hbK, mul_comm]

theorem associated_of_associated_at_height_one :
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] (a b : A),
      a ≠ 0 → b ≠ 0 →
      (∀ (q : Ideal A) [q.IsPrime], q.height = 1 →
        Associated (algebraMap A (Localization.AtPrime q) a)
          (algebraMap A (Localization.AtPrime q) b)) →
      Associated a b := by
  intro A _ _ _ _ a b ha hb h
  refine associated_of_dvd_dvd ?_ ?_
  · exact dvd_of_associated_at_height_one A b a ha (fun q _ h1 => (h q h1).symm)
  · exact dvd_of_associated_at_height_one A a b hb h

end GlobalTheory
