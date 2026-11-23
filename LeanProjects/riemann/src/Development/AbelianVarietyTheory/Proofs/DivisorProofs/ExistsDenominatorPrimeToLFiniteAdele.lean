import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasLevelStd
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)
open IsDedekindDomain
open GlobalTheory.CMVal (OF Af lattice IsBaseCond IsFinSetSplitPlacesCoprimeConductor condQ hatO)
open GlobalTheory.LatVal (OneOver)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (a0)

namespace GlobalTheory.HilbFam.AdeleDen

theorem val_nat {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) :
    Valued.v ((n : w.adicCompletion E)) = w.valuation E (algebraMap (𝓞 E) E (n : 𝓞 E)) := by
  rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w]
  congr 1
  rw [map_natCast]
  exact (map_natCast (algebraMap E (w.adicCompletion E)) n).symm

theorem val_nat_le {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) :
    Valued.v ((n : w.adicCompletion E)) ≤ 1 := by
  rw [val_nat]; exact w.valuation_le_one _

theorem exists_nat_mem {E : Type} [Field E] [NumberField E] {l : ℕ} (hl : l.Prime)
    (w : HeightOneSpectrum (𝓞 E)) (hw : (l : 𝓞 E) ∉ w.asIdeal) :
    ∃ m : ℕ, ¬ l ∣ m ∧ (m : 𝓞 E) ∈ w.asIdeal := by
  have h0 : Ideal.absNorm w.asIdeal ≠ 0 := fun h => w.ne_bot (Ideal.absNorm_eq_zero_iff.mp h)
  obtain ⟨k, m, hm, e⟩ := Nat.exists_eq_pow_mul_and_not_dvd h0 l hl.ne_one
  refine ⟨m, hm, ?_⟩
  have h := Ideal.absNorm_mem w.asIdeal
  rw [e] at h
  push_cast at h
  rcases w.isPrime.mem_or_mem h with h | h
  · exact absurd (w.isPrime.mem_of_pow_mem _ h) hw
  · exact h

theorem exists_local {E : Type} [Field E] [NumberField E] {l : ℕ} (hl : l.Prime)
    (w : HeightOneSpectrum (𝓞 E)) (hw : (l : 𝓞 E) ∉ w.asIdeal) (x : w.adicCompletion E) :
    ∃ m : ℕ, ¬ l ∣ m ∧ Valued.v ((m : w.adicCompletion E) * x) ≤ 1 := by
  obtain ⟨m, hm, hmw⟩ := exists_nat_mem hl w hw
  by_cases hx : Valued.v x = 0
  · exact ⟨m, hm, by simp [hx]⟩
  have h1 : Valued.v ((m : w.adicCompletion E)) < 1 := by
    rw [val_nat]; exact (w.valuation_lt_one_iff_mem _).mpr hmw
  obtain ⟨n, hn⟩ := exists_pow_lt₀ h1 (Units.mk0 _ (inv_ne_zero hx))
  refine ⟨m ^ n, fun h => hm (hl.dvd_of_dvd_pow h), ?_⟩
  rw [Nat.cast_pow, map_mul, map_pow]
  calc _ ≤ (Valued.v x)⁻¹ * Valued.v x := mul_le_mul_left hn.le _
    _ = 1 := inv_mul_cancel₀ hx

theorem exists_den_prime_to : ∀ (E : Type) [Field E] [NumberField E] (l : ℕ) (z : Af E), l.Prime → (∀ w : HeightOneSpectrum (𝓞 E), (l : 𝓞 E) ∈ w.asIdeal → Valued.v (z w) ≤ 1) → ∃ M : ℕ, ¬ l ∣ M ∧ ∀ w : HeightOneSpectrum (𝓞 E), Valued.v ((algebraMap E (Af E) (M : E) * z) w) ≤ 1 := by
  intro E _ _ l z hl hz
  have key : ∀ w : HeightOneSpectrum (𝓞 E), ∃ m : ℕ, ¬ l ∣ m ∧
      Valued.v ((m : w.adicCompletion E) * z w) ≤ 1 := by
    intro w
    by_cases hw : (l : 𝓞 E) ∈ w.asIdeal
    · exact ⟨1, hl.not_dvd_one, by simpa using hz w hw⟩
    · exact exists_local hl w hw _
  choose m hm hmz using key
  have hfin : {w : HeightOneSpectrum (𝓞 E) | ¬ z w ∈ w.adicCompletionIntegers E}.Finite :=
    Filter.eventually_cofinite.mp z.2
  refine ⟨∏ w ∈ hfin.toFinset, m w, ?_, fun w => ?_⟩
  · rw [hl.prime.dvd_finset_prod_iff]
    rintro ⟨w, -, h⟩
    exact hm w h
  · have e : ∀ M : ℕ, (algebraMap E (Af E) (M : E) * z) w = (M : w.adicCompletion E) * z w := by
      intro M
      rw [← map_natCast (algebraMap E (w.adicCompletion E)) M]
      rfl
    rw [e]
    by_cases hw : w ∈ hfin.toFinset
    · rw [← Finset.prod_erase_mul _ _ hw, Nat.cast_mul, mul_assoc, map_mul]
      exact mul_le_one' (val_nat_le _ _) (hmz w)
    · have : z w ∈ w.adicCompletionIntegers E := by simpa using hw
      rw [map_mul]
      exact mul_le_one' (val_nat_le _ _) this

end GlobalTheory.HilbFam.AdeleDen
