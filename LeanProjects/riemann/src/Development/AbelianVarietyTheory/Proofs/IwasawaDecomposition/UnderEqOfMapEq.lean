import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalToGlobal.Divisibility.Tuples
import Formalism.LocalToGlobal.UnitaryNorms.CharTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnderEqIffConjPl
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HostCmEmbeddingProperties

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr

namespace GlobalTheory.Mem.GoodPlace

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem plc_eq_absNorm (v : HeightOneSpectrum (𝓞 F)) (h : (Ideal.absNorm v.asIdeal).Prime) :
    Formalism.EigenvalueLevelCeiling.plc v = Ideal.absNorm v.asIdeal := by
  have := v.isPrime
  have : Nontrivial (𝓞 F ⧸ v.asIdeal) := Ideal.Quotient.nontrivial_iff.2 v.isPrime.ne_top
  unfold Formalism.EigenvalueLevelCeiling.plc
  apply CharP.ringChar_of_prime_eq_zero h
  rw [← map_natCast (Ideal.Quotient.mk v.asIdeal), Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.absNorm_mem _

theorem absNorm_map (h2 : Module.finrank F E = 2) (I : Ideal (𝓞 F)) :
    Ideal.absNorm (Ideal.map (algebraMap (𝓞 F) (𝓞 E)) I) = Ideal.absNorm I ^ 2 := by
  rw [Ideal.absNorm_algebraMap, ← h2]
  congr 1
  exact (Algebra.IsAlgebraic.finrank_of_isFractionRing (𝓞 F) F (𝓞 E) E).symm

theorem absNorm_under_dvd (P : HeightOneSpectrum (𝓞 E)) :
    Ideal.absNorm (P.under (𝓞 F)).asIdeal ∣ Ideal.absNorm P.asIdeal := by
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  exact AddSubgroup.card_dvd_of_injective
    (Ideal.quotientMap P.asIdeal (algebraMap (𝓞 F) (𝓞 E)) le_rfl).toAddMonoidHom Ideal.quotientMap_injective

theorem of_split (h2 : Module.finrank F E = 2) {v : HeightOneSpectrum (𝓞 F)} (hv : Formalism.L2.DIV.DegOne v)
    {Q Q' : HeightOneSpectrum (𝓞 E)} (hne : Q ≠ Q')
    (hm : Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal = Q.asIdeal * Q'.asIdeal) (hQ : Q.under (𝓞 F) = v) :
    Ideal.absNorm Q.asIdeal = Ideal.absNorm v.asIdeal ∧ ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 E) ∉ Q.asIdeal ^ 2 := by
  have hN : Ideal.absNorm Q.asIdeal * Ideal.absNorm Q'.asIdeal = Ideal.absNorm v.asIdeal ^ 2 := by
    rw [← map_mul, ← hm, absNorm_map h2]
  have h1 : Ideal.absNorm Q.asIdeal ≠ 1 := fun h => Q.isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 h)
  have h1' : Ideal.absNorm Q'.asIdeal ≠ 1 := fun h => Q'.isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 h)
  refine ⟨((Nat.Prime.mul_eq_prime_sq_iff hv.1 h1 h1').1 hN).1, ?_⟩
  intro hmem
  have hqv : ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 F) ∈ v.asIdeal := Ideal.absNorm_mem _
  obtain ⟨I, hI⟩ : v.asIdeal ∣ Ideal.span {((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 F)} :=
    Ideal.dvd_span_singleton.2 hqv
  have hd : Q.asIdeal ^ 2 ∣ Ideal.map (algebraMap (𝓞 F) (𝓞 E)) (Ideal.span {((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 F)}) := by
    rw [Ideal.map_span, Set.image_singleton, map_natCast]
    exact Ideal.dvd_span_singleton.2 hmem
  rw [hI, Ideal.map_mul, hm, pow_two, mul_assoc, mul_dvd_mul_iff_left Q.ne_bot] at hd
  rcases (Ideal.prime_of_isPrime Q.ne_bot Q.isPrime).dvd_or_dvd hd with h | h
  · exact hne (HeightOneSpectrum.ext (Q'.isMaximal.eq_of_le Q.isPrime.ne_top (Ideal.le_of_dvd h)).symm)
  · have hle : I ≤ v.asIdeal := by
      rw [← hQ]
      exact Ideal.map_le_iff_le_comap.1 (Ideal.le_of_dvd h)
    apply hv.2
    rw [← Ideal.span_singleton_le_iff_mem, hI, pow_two]
    exact Ideal.mul_mono_right hle

theorem under_eq_of_map_eq {v : HeightOneSpectrum (𝓞 F)} {Q : HeightOneSpectrum (𝓞 E)} {J : Ideal (𝓞 E)}
    (hm : Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal = Q.asIdeal * J) : Q.under (𝓞 F) = v := by
  refine (HeightOneSpectrum.ext (v.isMaximal.eq_of_le (Q.under (𝓞 F)).isPrime.ne_top ?_)).symm
  exact Ideal.map_le_iff_le_comap.1 (hm ▸ Ideal.mul_le_left)

theorem map_eq_mul (h2 : Module.finrank F E = 2) {P P' : HeightOneSpectrum (𝓞 E)} (hne : P ≠ P')
    (hu : P'.under (𝓞 F) = P.under (𝓞 F)) :
    Ideal.map (algebraMap (𝓞 F) (𝓞 E)) (P.under (𝓞 F)).asIdeal = P.asIdeal * P'.asIdeal := by
  have hle : Ideal.map (algebraMap (𝓞 F) (𝓞 E)) (P.under (𝓞 F)).asIdeal ≤ P.asIdeal * P'.asIdeal := by
    rw [Ideal.mul_eq_inf_of_isCoprime (HeightOneSpectrum.isCoprime_of_ne P P' hne)]
    refine le_inf Ideal.map_comap_le ?_
    rw [← hu]
    exact Ideal.map_comap_le
  obtain ⟨J, hJ⟩ := Ideal.dvd_iff_le.2 hle
  have hN := absNorm_map h2 (P.under (𝓞 F)).asIdeal
  obtain ⟨a, ha⟩ := absNorm_under_dvd (F := F) P
  obtain ⟨b, hb⟩ := absNorm_under_dvd (F := F) P'
  rw [hu] at hb
  have h0 : Ideal.absNorm (P.under (𝓞 F)).asIdeal ≠ 0 := fun h => (P.under (𝓞 F)).ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  rw [hJ, map_mul, map_mul, ha, hb] at hN
  have h3 : (a * b) * Ideal.absNorm J = 1 := by
    apply mul_left_cancel₀ (pow_ne_zero 2 h0)
    rw [mul_one]
    refine Eq.trans ?_ hN
    ring
  rw [hJ, Ideal.absNorm_eq_one_iff.1 (Nat.eq_one_of_mul_eq_one_left h3), Ideal.mul_top]

theorem goodPl_iff (h2 : Module.finrank F E = 2) (S : Set ℕ) (P : HeightOneSpectrum (𝓞 E)) :
    Formalism.L2.DIV.GoodPl E S (P.under (𝓞 F)) ↔ ((∃ P', P ≠ P' ∧ P'.under (𝓞 F) = P.under (𝓞 F)) ∧
      (Ideal.absNorm P.asIdeal).Prime ∧ ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2 ∧
      Ideal.absNorm P.asIdeal ∉ S) := by
  constructor
  · rintro ⟨⟨Q, Q', hne, hm⟩, hv, hS⟩
    obtain ⟨P', hne', hm'⟩ : ∃ P', P ≠ P' ∧
        Ideal.map (algebraMap (𝓞 F) (𝓞 E)) (P.under (𝓞 F)).asIdeal = P.asIdeal * P'.asIdeal := by
      have hle : Q.asIdeal * Q'.asIdeal ≤ P.asIdeal := by
        rw [← hm]
        exact Ideal.map_comap_le
      rcases P.isPrime.mul_le.1 hle with h | h
      · obtain rfl : Q = P := HeightOneSpectrum.ext (Q.isMaximal.eq_of_le P.isPrime.ne_top h)
        exact ⟨Q', hne, hm⟩
      · obtain rfl : Q' = P := HeightOneSpectrum.ext (Q'.isMaximal.eq_of_le P.isPrime.ne_top h)
        exact ⟨Q, hne.symm, by rw [hm, mul_comm]⟩
    obtain ⟨e, hn⟩ := of_split h2 hv hne' hm' rfl
    rw [plc_eq_absNorm _ hv.1] at hS
    rw [e]
    exact ⟨⟨P', hne', under_eq_of_map_eq (hm'.trans (mul_comm _ _))⟩, hv.1, hn, hS⟩
  · rintro ⟨⟨P', hne, hu⟩, hp, hn, hS⟩
    have e : Ideal.absNorm (P.under (𝓞 F)).asIdeal = Ideal.absNorm P.asIdeal :=
      ((Nat.dvd_prime hp).1 (absNorm_under_dvd P)).resolve_left fun h =>
        (P.under (𝓞 F)).isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 h)
    refine ⟨⟨P, P', hne, map_eq_mul h2 hne hu⟩, ⟨e ▸ hp, fun h => hn ?_⟩, ?_⟩
    · rw [e] at h
      have h3 := Ideal.mem_map_of_mem (algebraMap (𝓞 F) (𝓞 E)) h
      rw [map_natCast, Ideal.map_pow] at h3
      exact Ideal.pow_right_mono Ideal.map_comap_le 2 h3
    · rw [plc_eq_absNorm _ (e ▸ hp), e]
      exact hS

end General

theorem isSplitPl_iff {R : Ranks} (H : Formalism.BasicNotions.Host R) (P : HeightOneSpectrum (𝓞 H.E)) :
    IsSplitPl H P ↔ ∃ P', P ≠ P' ∧ P'.under (𝓞 H.F) = P.under (𝓞 H.F) := by
  obtain ⟨c, hc, hcm, -⟩ := GlobalTheory.Mem.HostCM.host_cm R H
  constructor
  · rintro ⟨x, hx, hy⟩
    obtain ⟨P', hP', -⟩ := existsUnique_conjPl c.toRingEquiv P
    refine ⟨P', ?_, (under_eq_iff_conjPl c hcm.rank hcm.ne P P').2 (Or.inr hP')⟩
    rintro rfl
    exact hy (RingOfIntegers.mapRingEquiv c.toRingEquiv x) (hc x) (((conjPl_iff_mem _ P P).1 hP' x _ rfl).1 hx)
  · rintro ⟨P', hne, hu⟩
    have hP' := ((under_eq_iff_conjPl c hcm.rank hcm.ne P P').1 hu).resolve_left hne.symm
    rw [conjPl_iff_mem] at hP'
    by_contra hn
    unfold IsSplitPl at hn
    push Not at hn
    refine hne (HeightOneSpectrum.ext (P'.isMaximal.eq_of_le P.isPrime.ne_top fun y hy => ?_).symm)
    have hxy : (y : H.E) = c.toRingEquiv ((RingOfIntegers.mapRingEquiv c.toRingEquiv).symm y : 𝓞 H.E) :=
      congrArg (fun z : 𝓞 H.E => (z : H.E)) ((RingOfIntegers.mapRingEquiv c.toRingEquiv).apply_symm_apply y).symm
    obtain ⟨z, hz, hzP⟩ := hn _ ((hP' _ y hxy).2 hy)
    have e : z = y := RingOfIntegers.ext (hz.trans ((hc _).symm.trans hxy.symm))
    exact e ▸ hzP

open Classical in

theorem goodPl_under_iff : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (S : Set ℕ) (P : HeightOneSpectrum (𝓞 H.E)), Formalism.L2.DIV.GoodPl H.E S (P.under (𝓞 H.F)) ↔ (IsSplitPl H P ∧ (Ideal.absNorm P.asIdeal).Prime ∧ ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 H.E) ∉ P.asIdeal ^ 2 ∧ Ideal.absNorm P.asIdeal ∉ S) := by
  intro R H S P
  obtain ⟨c, -, hcm, -⟩ := GlobalTheory.Mem.HostCM.host_cm R H
  rw [isSplitPl_iff]
  exact goodPl_iff hcm.rank S P

end GlobalTheory.Mem.GoodPlace
