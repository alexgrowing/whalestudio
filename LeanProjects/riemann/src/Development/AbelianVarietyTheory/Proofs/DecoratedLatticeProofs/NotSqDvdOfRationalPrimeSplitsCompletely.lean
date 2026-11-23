import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryDatumLevelPrimeSplitDegreeGramFacts
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StandardAdditiveCharacterLocalNeOneSplitPrime

open NumberField IsDedekindDomain

namespace GlobalTheory.St.G.SplitUnram

theorem not_sq_dvd_of_splitsIn : ∀ (E : Type) [Field E] [NumberField E] (T : ℕ), T.Prime → GlobalTheory.St.G.SplitsIn E T →
    ∀ w : HeightOneSpectrum (𝓞 E), (T : 𝓞 E) ∈ w.asIdeal → ¬ w.asIdeal ^ 2 ∣ Ideal.span {(T : 𝓞 E)} := by
  intro E _ _ T hT hs w hw hdvd
  have := w.isPrime
  have hnd := GlobalTheory.St.G.PsiLoc.not_dvd_different hT hs w.asIdeal hw
  have hun : Algebra.IsUnramifiedAt ℤ w.asIdeal := not_dvd_differentIdeal_iff.1 hnd
  have he : w.asIdeal.ramificationIdx ℤ = 1 := Ideal.ramificationIdx_eq_one_iff.2 hun
  have hp : Prime (T : ℤ) := Nat.prime_iff_prime_int.mp hT
  have hmax : (Ideal.span {(T : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  have hmap : Ideal.map (algebraMap ℤ (𝓞 E)) (Ideal.span {(T : ℤ)}) = Ideal.span {((T : ℕ) : 𝓞 E)} := by
    rw [Ideal.map_span]; simp
  have hle : Ideal.map (algebraMap ℤ (𝓞 E)) (Ideal.span {(T : ℤ)}) ≤ w.asIdeal := by
    rw [hmap, Ideal.span_le]; simpa using hw
  have : w.asIdeal.LiesOver (Ideal.span {(T : ℤ)}) :=
    ⟨hmax.eq_of_le (Ideal.comap_ne_top _ w.isPrime.ne_top) (Ideal.map_le_iff_le_comap.mp hle)⟩
  have hb : Ideal.span {(T : ℤ)} ≠ ⊥ := by simpa using hT.ne_zero
  rw [← Ideal.ramificationIdx'_eq_ramificationIdx (Ideal.span {(T : ℤ)}) w.asIdeal hb] at he
  have h2 := (Ideal.ramificationIdx'_ne_one_iff hle).2
  rw [hmap] at h2
  exact h2 (Ideal.le_of_dvd hdvd) he

end GlobalTheory.St.G.SplitUnram
