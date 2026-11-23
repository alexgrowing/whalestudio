import Mathlib
import Formalism.GL3MeanSquares.PrimeCountAsymptoticInProgressions
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Formalism.CyclotomicNorms.StatementI
import Development.AbelianVarietyTheory.Definitions.Foundations.RayPrimes
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NcardPrimesOverOfStabilizer

open Finset ArithmeticFunction NumberField IsDedekindDomain Filter Topology GlobalTheory.Mem.An Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab
open scoped nonZeroDivisors

namespace GlobalTheory.HostSplit

theorem absNorm_eq_of_ncard_placesOver (E : Type) [Field E] [NumberField E] [IsGalois ℚ E] {p : ℕ}
    (hp : p.Prime) (h : (placesOver E p).ncard = Module.finrank ℚ E) :
    ∀ v ∈ placesOver E p, Ideal.absNorm v.asIdeal = p := by
  intro v hv
  have : IsGaloisGroup (E ≃ₐ[ℚ] E) ℤ (𝓞 E) := IsGaloisGroup.of_isFractionRing _ _ _ ℚ E
  have hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible
  have hPp := v.isPrime
  have hlo : v.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) := by
    refine ⟨hmax.eq_of_le (Ideal.IsPrime.under ℤ v.asIdeal).ne_top ?_⟩
    rw [Ideal.span_le, Set.singleton_subset_iff]
    show algebraMap ℤ (𝓞 E) ((p : ℕ) : ℤ) ∈ v.asIdeal
    rw [map_natCast]
    exact hv
  have hf := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn (Ideal.span {(p : ℤ)}) (𝓞 E)
    (E ≃ₐ[ℚ] E)
  rw [← ncard_placesOver E hp, h, IsGalois.card_aut_eq_finrank,
    Ideal.inertiaDegIn_eq_inertiaDeg (Ideal.span {(p : ℤ)}) v.asIdeal (E ≃ₐ[ℚ] E)] at hf
  have hpos : 0 < Module.finrank ℚ E := Module.finrank_pos
  have h1 := Nat.eq_of_mul_eq_mul_left hpos (hf.trans (mul_one _).symm)
  have h2 := Nat.eq_one_of_mul_eq_one_left h1
  have h3 := Ideal.absNorm_pow_inertiaDeg (Ideal.span {(p : ℤ)}) v.asIdeal
  rw [h2, pow_one] at h3
  rw [← h3]
  simp

theorem split_completely_of_modEq_one : ∀ (R : Ranks) (H : Host R) (p : ℕ), p.Prime →
    p ≡ 1 [MOD H.QS * H.q * H.d] →
    (placesOver H.E p).ncard = Module.finrank ℚ H.E ∧ H.cls p = PrimeClass.splitK ∧
      ∀ v ∈ placesOver H.E p, Ideal.absNorm v.asIdeal = p := by
  intro R H p hp hc
  have hn : 0 < H.QS := H.QS_pos
  have hq : 0 < H.q := H.hyp.1.pos
  have hd : 1 < H.d := H.hyp.2.1.one_lt
  have hlt : 1 < H.QS * H.q * H.d := by
    have : 0 < H.QS * H.q := by positivity
    nlinarith
  have hm : p % (H.QS * H.q * H.d) = 1 := by
    rw [Nat.ModEq] at hc
    rw [hc, Nat.mod_eq_of_lt hlt]
  obtain ⟨h1, h2⟩ := split_of_one_mod R H p hp hm
  have hG : IsGalois ℚ H.E := H.galois
  exact ⟨h1, h2, absNorm_eq_of_ncard_placesOver H.E hp h1⟩

end GlobalTheory.HostSplit
