import Mathlib
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModGDefs
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModGBasic
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModPrincNorm
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.IsIntegralOfRoot
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModLatTau
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModJTau
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModCMPoint
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModVanish
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModFrobSer
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModKronPt

noncomputable section
open scoped BigOperators Classical UpperHalfPlane
open NumberField IsDedekindDomain Formalism.L2.Th1.CM Neutral.HilbertClassField

namespace ReciprocityTheory.ChartRestriction.L1

theorem natCard_mem {E Ω : Type*} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] {A : ValuationSubring Ω}
    {v : HeightOneSpectrum (𝓞 E)} (h : LiesAbove A v) :
    ((Nat.card (𝓞 E ⧸ v.asIdeal) : ℕ) : Ω) ∈ A.nonunits := by
  have hmem : ((Nat.card (𝓞 E ⧸ v.asIdeal) : ℕ) : 𝓞 E) ∈ v.asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
    rcases finite_or_infinite (𝓞 E ⧸ v.asIdeal) with hf | hf
    · have := Fintype.ofFinite (𝓞 E ⧸ v.asIdeal)
      rw [Nat.card_eq_fintype_card]
      exact Nat.cast_card_eq_zero _
    · rw [Nat.card_eq_zero_of_infinite, Nat.cast_zero]
  have h2 := (h _).mpr hmem
  simpa using h2

theorem frobCong {d : ℕ} {L : PeriodPair} (hsf : Squarefree d) (hd : d % 4 = 3) (hL : HasCMBy d L)
    (x : Om d) (hx : (x : ℂ) = jInv L) (A : ValuationSubring (Om d)) (v : HeightOneSpectrum (𝓞 (KQ d)))
    (hA : LiesAbove A v) (hp : (Nat.card (𝓞 (KQ d) ⧸ v.asIdeal)).Prime)
    (hv : ClassGroup.mk0 ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩ = 1) :
    x ^ Nat.card (𝓞 (KQ d) ⧸ v.asIdeal) - x ∈ A.nonunits := by
  set N := Nat.card (𝓞 (KQ d) ⧸ v.asIdeal) with hN
  have hd0 : 0 < d := by omega
  obtain ⟨c, τ, hτ⟩ := latTau L
  have hj : jInv L = jT τ := jInv_eq_jT hτ
  obtain ⟨a, b, hab⟩ := princ_form hsf hd v hv
  obtain ⟨A', B', C', D', h1, h2, h3⟩ := cmPoint hd0 hL hτ a b
  have hG : Gm N τ = 0 := by
    apply Gm_vanish hp.pos τ A' B' C' D'
    · linarith
    · rw [← h1, h2]
      ring
  obtain ⟨r, hr, hrel⟩ := kronPt hp hG
  obtain ⟨r0, hr0m, hr0⟩ := one_sub_zeta_pow hp
  have hzint : IsIntegral ℤ (zetaC N) := (zetaC_isPrimitiveRoot hp.ne_zero).isIntegral hp.pos
  have hr0int : IsIntegral ℤ r0 := by
    have hle : Rm N ≤ (integralClosure ℤ ℂ).toSubring :=
      Subring.closure_le.mpr (Set.singleton_subset_iff.mpr hzint)
    exact hle hr0m
  obtain ⟨r', hr'c, hr'i⟩ := exists_Om d hr
  obtain ⟨r0', hr0'c, hr0'i⟩ := exists_Om d hr0int
  have hC : (((x ^ N - x) ^ (2 * N) : Om d) : ℂ) = (((N : Om d) * r0' * r' ^ N : Om d) : ℂ) := by
    push_cast
    rw [hr'c, hr0'c, hx, hj, pow_mul, hrel, mul_pow, hr0]
  have hEq : (x ^ N - x) ^ (2 * N) = (N : Om d) * r0' * r' ^ N := Subtype.ext hC
  have hNu := natCard_mem hA
  rw [ValuationSubring.mem_nonunits_iff] at hNu ⊢
  have hv1 : A.valuation r0' ≤ 1 := (A.valuation_le_one_iff _).mpr (mem_of_isIntegral A hr0'i)
  have hv2 : A.valuation r' ≤ 1 := (A.valuation_le_one_iff _).mpr (mem_of_isIntegral A hr'i)
  have hv3 : A.valuation ((x ^ N - x) ^ (2 * N)) < 1 := by
    rw [hEq, map_mul, map_mul, map_pow]
    exact mul_lt_one_of_lt_of_le (mul_lt_one_of_lt_of_le hNu hv1) (pow_le_one' hv2 _)
  by_contra hcon
  rw [map_pow] at hv3
  exact absurd hv3 (not_lt.mpr (one_le_pow_of_one_le' (not_lt.mp hcon) _))

end ReciprocityTheory.ChartRestriction.L1
