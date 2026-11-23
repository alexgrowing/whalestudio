import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.JetOpIntegral
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AbsNormSpanInvol

namespace GlobalTheory.ColPeriod

open NumberField IsDedekindDomain Formalism.L2.Col Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance (DegOneUnram)

section Split

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem absNorm_eq_of_split_factor (h2 : Module.finrank F E = 2) {v : HeightOneSpectrum (𝓞 F)} (hv : DegOne v)
    {P P' : HeightOneSpectrum (𝓞 E)} (hne : P ≠ P')
    (hm : v.asIdeal.map (algebraMap (𝓞 F) (𝓞 E)) = P.asIdeal * P'.asIdeal) :
    Ideal.absNorm P.asIdeal = Ideal.absNorm v.asIdeal ∧ ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2 := by
  obtain ⟨hq, hq2⟩ := hv
  constructor
  · have hr : Module.finrank (𝓞 F) (𝓞 E) = 2 := by
      rw [← h2]
      exact (IsFractionRing.finrank_eq (𝓞 F) F (𝓞 E) E).symm
    have h1 := Ideal.absNorm_algebraMap (𝓞 F) (𝓞 E) v.asIdeal
    rw [hm, hr, map_mul] at h1
    have hP : Ideal.absNorm P.asIdeal ≠ 1 := by
      rw [Ne, Ideal.absNorm_eq_one_iff]; exact P.isPrime.ne_top
    have hP' : Ideal.absNorm P'.asIdeal ≠ 1 := by
      rw [Ne, Ideal.absNorm_eq_one_iff]; exact P'.isPrime.ne_top
    obtain ⟨k, hk, e⟩ := (Nat.dvd_prime_pow hq).1 (Dvd.intro _ h1)
    interval_cases k
    · exact absurd (by simpa using e) hP
    · simpa using e
    · rw [e] at h1
      exact absurd ((Nat.mul_eq_left (pow_pos hq.pos 2).ne').1 h1) hP'
  · intro hmem
    obtain ⟨I, hI⟩ : v.asIdeal ∣ Ideal.span {((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 F)} := by
      rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
      exact Ideal.absNorm_mem _
    have h3 := congrArg (Ideal.map (algebraMap (𝓞 F) (𝓞 E))) hI
    rw [Ideal.map_span, Set.image_singleton, map_natCast, Ideal.map_mul, hm, mul_assoc] at h3
    have h4 : P.asIdeal * P.asIdeal ∣ P.asIdeal * (P'.asIdeal * I.map (algebraMap (𝓞 F) (𝓞 E))) := by
      rw [← h3, ← sq, Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
      exact hmem
    have h5 := (mul_dvd_mul_iff_left P.ne_bot).1 h4
    rcases P.prime.dvd_or_dvd h5 with h6 | h6
    · rw [Ideal.dvd_iff_le] at h6
      exact hne (HeightOneSpectrum.ext (P'.isMaximal.eq_of_le P.isPrime.ne_top h6).symm)
    · rw [Ideal.dvd_iff_le, Ideal.map_le_iff_le_comap] at h6
      have h7 : v.asIdeal ≤ P.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E)) := by
        rw [← Ideal.map_le_iff_le_comap, hm]
        exact (Ideal.mul_le_inf).trans inf_le_left
      rw [← v.isMaximal.eq_of_le (Ideal.comap_ne_top _ P.isPrime.ne_top) h7] at h6
      apply hq2
      rw [← Ideal.span_singleton_le_iff_mem, hI, sq]
      exact Ideal.mul_mono_right h6

theorem absNorm_eq_of_splitAt (h2 : Module.finrank F E = 2) {v : HeightOneSpectrum (𝓞 F)} (hs : SplitAt E v)
    (hv : DegOne v) {Q : HeightOneSpectrum (𝓞 E)} (hQ : Q.asIdeal.under (𝓞 F) = v.asIdeal) :
    Ideal.absNorm Q.asIdeal = Ideal.absNorm v.asIdeal ∧ ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 E) ∉ Q.asIdeal ^ 2 := by
  obtain ⟨P, P', hne, hm⟩ := hs
  have h1 : P.asIdeal * P'.asIdeal ≤ Q.asIdeal := by
    rw [← hm, Ideal.map_le_iff_le_comap, ← hQ]
  rcases Q.isPrime.mul_le.1 h1 with h | h
  · obtain rfl : P = Q := HeightOneSpectrum.ext (P.isMaximal.eq_of_le Q.isPrime.ne_top h)
    exact absNorm_eq_of_split_factor h2 hv hne hm
  · obtain rfl : P' = Q := HeightOneSpectrum.ext (P'.isMaximal.eq_of_le Q.isPrime.ne_top h)
    exact absNorm_eq_of_split_factor h2 hv hne.symm (hm.trans (mul_comm _ _))

omit [NumberField E] [Field E] [Algebra F E] in

theorem plc_eq_absNorm {v : HeightOneSpectrum (𝓞 F)} (hq : (Ideal.absNorm v.asIdeal).Prime) :
    Formalism.EigenvalueLevelCeiling.plc v = Ideal.absNorm v.asIdeal := by
  have h6 : ringChar (𝓞 F ⧸ v.asIdeal) ∣ Ideal.absNorm v.asIdeal := by
    rw [← ringChar.spec, ← map_natCast (Ideal.Quotient.mk v.asIdeal), Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.absNorm_mem _
  have := v.isPrime
  rcases (Nat.dvd_prime hq).1 h6 with h7 | h7
  · exact absurd h7 CharP.ringChar_ne_one
  · exact h7

end Split

theorem degOneUnram_of_mem_vG {X : Fields} {Pr : Primes X} (hX : X.Ok) (hPr : Pr.Ok) (i : Fin 2)
    {P : HeightOneSpectrum (𝓞 X.E)} (hP : P ∈ Pr.vG i) : DegOneUnram P := by
  have hcc : ∀ x, X.conjO (X.conjO x) = x := fun x => RingOfIntegers.ext (star_star (x : X.E))
  have hE : Module.finrank ℚ X.E = 2 * X.f := by
    rw [← Module.finrank_mul_finrank ℚ X.F X.E, hX.rankE, ← hX.card_Tau, mul_comm]
    rfl
  have hn : qOf P = Pr.g i := hPr.vG_norm i P hP
  refine ⟨hn ▸ hPr.g_prime i, ?_⟩
  rw [hn]
  refine GlobalTheory.SplitUnram.natCast_notMem_sq X.E X.conjO (X.conjO (Pr.piG i)) (Pr.g i) hcc (hPr.g_prime i) ?_ ?_ ?_
    (hPr.vG_norm i) P hP
  · rw [hcc, mul_comm]; exact hPr.piG_norm i
  · rw [hcc]; exact (hPr.piG_cop i).symm
  · rw [hE, ← hPr.vG_card i]; rfl

theorem levelPrimes : LevelPrimes := by
  classical
  intro X Pr sel S mu hX hPr hsel P
  by_cases hP : P.1 ∈ Pr.vGs
  · refine ⟨?_, fun h => absurd hP h⟩
    rcases Finset.mem_union.1 hP with h | h
    exacts [degOneUnram_of_mem_vG hX hPr 0 h, degOneUnram_of_mem_vG hX hPr 1 h]
  · rcases Finset.mem_union.1 P.2 with h1 | h1
    · exact absurd h1 hP
    unfold QE at h1
    split_ifs at h1 with h2
    · obtain ⟨v0, hv0, e⟩ := Finset.mem_image.1 h1
      have hv1 : v0 ∈ Qprime (mu : Chr X.F X.E X.K) := by simpa using hv0
      have hgood : GoodPl X.E S v0 := by
        by_contra hn
        have h4 := (Subgroup.mem_inf.1 mu.2).2
        exact hv1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 h4 v0) hn)
      obtain ⟨h3, h4⟩ := absNorm_eq_of_splitAt hX.rankE hgood.1 hgood.2.1 (Q := P.1) (e ▸ hsel v0)
      have h5 : qOf P.1 = Ideal.absNorm v0.asIdeal := h3
      refine ⟨⟨h5 ▸ hgood.2.1.1, h5 ▸ h4⟩, fun _ => ?_⟩
      rw [h5, ← plc_eq_absNorm hgood.2.1.1]
      exact hgood.2.2
    · simp at h1

end GlobalTheory.ColPeriod
