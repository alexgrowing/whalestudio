import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BoundedPowersOrExistsValuationSubringDvdStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdicCompletionValuationRingCompleteValuationDomaStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdicCompletionPrincipalPerfectStatement
open scoped NNReal

namespace GlobalTheory

theorem perfectRing_valuationSubring_of_isAlgClosed (l : ℕ) [Fact l.Prime] {L : Type} [Field L]
    [IsAlgClosed L] (V : ValuationSubring L) [CharP V l] : PerfectRing V l := by
  haveI : ExpChar V l := ExpChar.prime Fact.out
  refine PerfectRing.ofSurjective V l ?_
  intro v
  have hl0 : l ≠ 0 := (Fact.out : l.Prime).ne_zero
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq (v : L) (Nat.pos_of_ne_zero hl0)
  have hyV : y ∈ V := by
    rw [← V.valuation_le_one_iff]
    have hv : V.valuation (v : L) ≤ 1 := (V.valuation_le_one_iff _).2 v.2
    rw [← hy, map_pow] at hv
    exact (pow_le_one_iff_of_nonneg (zero_le') hl0).1 hv
  refine ⟨⟨y, hyV⟩, ?_⟩
  apply Subtype.ext
  simp [frobenius_def, hy]

theorem s_points_kpt : ∀ (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] (u x : R), ((l : ℕ) : R) = 0 →
    u ∈ nonZeroDivisors R → (∀ r, IsUnit (1 - u * r)) →
    (∀ (O : Type) [CommRing O] [IsDomain O] [ValuationRing O] [CharP O l] [PerfectRing O l]
      (f : R →+* O), f u ≠ 0 → ¬ IsUnit (f u) → IsAdicComplete (Ideal.span {f u}) O → f x = 0) →
    ∀ M : ℕ, ∃ c : ℕ, ∀ n : ℕ, u ^ (M * n) ∣ u ^ c * x ^ n := by
  intro l _ R _ u x hl hu hrad H M
  rcases GlobalTheory.T.pow_dvd_bound_or_exists_valuationSubring_dvd R u x M hu hrad with h | ⟨L, _, _, V, f, hfu, hfnu, hdvd⟩
  · exact h
  exfalso
  haveI : CharP V l := (CharP.charP_iff_prime_eq_zero Fact.out).2 (by
    rw [← map_natCast f, hl, map_zero])
  haveI : PerfectRing V l := perfectRing_valuationSubring_of_isAlgClosed l V
  obtain ⟨hdom, hpre, hne, hnu, hcomp⟩ := GlobalTheory.T.adicCompletion_valuationRing_complete_valuationDomain V (f u) hfu hfnu
  obtain ⟨hl', hbij⟩ := GlobalTheory.T.adicCompletion_principal_perfect l V (f u)
  set O := AdicCompletion (Ideal.span {f u}) V
  haveI : IsDomain O := hdom
  haveI : ValuationRing O := { toPreValuationRing := hpre }
  haveI : CharP O l := (CharP.charP_iff_prime_eq_zero Fact.out).2 hl'
  haveI : PerfectRing O l := ⟨hbij⟩
  let g : R →+* O := (algebraMap V O).comp f
  have hgx : g x = 0 := H O g hne hnu hcomp
  have hd : g x ∣ g u ^ M := by
    simpa [g, map_pow] using map_dvd (algebraMap V O) hdvd
  rw [hgx, zero_dvd_iff] at hd
  exact hne (by_contra fun h => pow_ne_zero M h hd)

end GlobalTheory
