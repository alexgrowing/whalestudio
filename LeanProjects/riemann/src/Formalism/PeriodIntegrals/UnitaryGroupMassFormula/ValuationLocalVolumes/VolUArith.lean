import Mathlib
import ReciprocityTheory.GaloisValuations.ArithOfA
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.VolTSt

noncomputable section

namespace Formalism.L2.SG.Pf.NcVal.VolUAr

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Ideal

section V

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

theorem val_natCast_of (g : ℕ) (hg1 : (g : 𝓞 F) ∈ v.asIdeal) (hg2 : (g : 𝓞 F) ∉ v.asIdeal ^ 2) :
    Valued.v (((g : v.adicCompletionIntegers F) : v.adicCompletion F)) = WithZero.exp (-1 : ℤ) := by
  have e : (((g : v.adicCompletionIntegers F) : v.adicCompletion F)) = (((g : 𝓞 F) : F) : v.adicCompletion F) := by
    push_cast
    exact (map_natCast (algebraMap F (v.adicCompletion F)) g).symm
  rw [e, valuedAdicCompletion_eq_valuation', valuation_of_algebraMap]
  have hg0 : (g : 𝓞 F) ≠ 0 := by
    rintro h
    exact hg2 (h ▸ Ideal.zero_mem _)
  have h1 := (intValuation_le_pow_iff_dvd v (g : 𝓞 F) 1).mpr (by rwa [pow_one, Ideal.dvd_span_singleton])
  have h2 : ¬ v.intValuation (g : 𝓞 F) ≤ WithZero.exp (-((2 : ℕ) : ℤ)) := by
    rw [intValuation_le_pow_iff_dvd, Ideal.dvd_span_singleton]
    exact hg2
  rw [intValuation_eq_exp_neg_multiplicity v hg0] at h1 h2 ⊢
  rw [WithZero.exp_le_exp] at h1 h2
  congr 1
  omega

end V

theorem split_transport {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] (e : K ≃+* L)
    (l : ℕ) (h : {w : HeightOneSpectrum (𝓞 L) | ((l : ℕ) : 𝓞 L) ∈ w.asIdeal}.ncard = Module.finrank ℚ L) :
    {w : HeightOneSpectrum (𝓞 K) | ((l : ℕ) : 𝓞 K) ∈ w.asIdeal}.ncard = Module.finrank ℚ K := by
  set φ : 𝓞 K ≃+* 𝓞 L := NumberField.RingOfIntegers.mapRingEquiv e with hφ
  rw [(e.toRatAlgEquiv).toLinearEquiv.finrank_eq, ← h]
  refine Set.ncard_congr
    (fun w _ => (⟨w.asIdeal.map φ, Ideal.map_isPrime_of_equiv φ,
      fun hb => w.ne_bot ((Ideal.map_eq_bot_iff_of_injective φ.injective).mp hb)⟩ : HeightOneSpectrum (𝓞 L)))
    ?_ ?_ ?_
  · intro w hw
    have h1 := Ideal.mem_map_of_mem φ hw
    rw [map_natCast] at h1
    exact h1
  · intro a b _ _ hab
    have h1 : a.asIdeal.map φ = b.asIdeal.map φ := congrArg HeightOneSpectrum.asIdeal hab
    have h2 := congrArg (Ideal.comap φ) h1
    rw [Ideal.comap_map_of_bijective φ φ.bijective, Ideal.comap_map_of_bijective φ φ.bijective] at h2
    exact HeightOneSpectrum.ext h2
  · intro w' hw'
    have hne : w'.asIdeal.comap φ ≠ ⊥ := by
      intro hb
      apply w'.ne_bot
      rw [← Ideal.map_comap_of_surjective φ φ.surjective w'.asIdeal, hb, Ideal.map_bot]
    refine ⟨⟨w'.asIdeal.comap φ, Ideal.IsPrime.comap φ, hne⟩, ?_, ?_⟩
    · show _ ∈ Ideal.comap φ w'.asIdeal
      rw [Ideal.mem_comap, map_natCast]
      exact hw'
    · exact HeightOneSpectrum.ext (Ideal.map_comap_of_surjective φ φ.surjective w'.asIdeal)

section K

variable {K : Type} [Field K] [NumberField K]

private theorem liesOver_span_of_natCast_mem' (l : ℕ) [Fact l.Prime] (w : Ideal (𝓞 K)) [w.IsPrime]
    (hw : ((l : ℕ) : 𝓞 K) ∈ w) : w.LiesOver (Ideal.span {((l : ℕ) : ℤ)}) := by
  refine ⟨(Int.ideal_span_isMaximal_of_prime l).eq_of_le (Ideal.IsPrime.ne_top (Ideal.IsPrime.under ℤ w)) ?_⟩
  rw [Ideal.span_le, Set.singleton_subset_iff]
  show _ ∈ Ideal.comap (algebraMap ℤ (𝓞 K)) w
  rw [Ideal.mem_comap]
  simpa using hw

theorem locDeg_one (l : ℕ) [hl : Fact l.Prime]
    (h : {w : HeightOneSpectrum (𝓞 K) | ((l : ℕ) : 𝓞 K) ∈ w.asIdeal}.ncard = Module.finrank ℚ K)
    (w : HeightOneSpectrum (𝓞 K)) (hw : ((l : ℕ) : 𝓞 K) ∈ w.asIdeal) :
    w.asIdeal.ramificationIdx ℤ = 1 ∧ w.asIdeal.inertiaDeg ℤ = 1 := by
  have hmaxl := Int.ideal_span_isMaximal_of_prime l
  have hl0 : ((l : ℕ) : 𝓞 K) ≠ 0 := Nat.cast_ne_zero.mpr hl.out.ne_zero
  have hsum := Ideal.sum_ramification_inertia_eq_finrank (Ideal.span {((l : ℕ) : ℤ)}) (𝓞 K)
  rw [NumberField.RingOfIntegers.rank] at hsum
  have hcard : Fintype.card ((Ideal.span {((l : ℕ) : ℤ)}).primesOver (𝓞 K)) = Module.finrank ℚ K := by
    rw [← h, ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
    symm
    refine Set.ncard_congr (fun w _ => w.asIdeal) (fun w hw => ⟨w.isPrime, liesOver_span_of_natCast_mem' l w.asIdeal hw⟩)
      (fun a b _ _ hab => HeightOneSpectrum.ext hab) ?_
    intro Q hQ
    haveI := hQ.1
    haveI := hQ.2
    have hmem : ((l : ℕ) : 𝓞 K) ∈ Q := by
      have h3 : ((l : ℕ) : ℤ) ∈ Q.under ℤ := by
        rw [← Ideal.over_def Q (Ideal.span {((l : ℕ) : ℤ)})]
        exact Ideal.mem_span_singleton_self _
      have h4 := Ideal.mem_comap.mp h3
      simpa using h4
    refine ⟨⟨Q, hQ.1, ?_⟩, hmem, rfl⟩
    intro hb
    rw [hb, Ideal.mem_bot] at hmem
    exact hl0 hmem
  have hpos : ∀ q ∈ (Finset.univ : Finset ((Ideal.span {((l : ℕ) : ℤ)}).primesOver (𝓞 K))),
      (fun _ => 1) q ≤ q.1.ramificationIdx ℤ * q.1.inertiaDeg ℤ := by
    intro q _
    exact Nat.one_le_iff_ne_zero.mpr
      (Nat.mul_ne_zero (Ideal.ramificationIdx_pos q.1 ℤ).ne' (Ideal.inertiaDeg_pos q.1 ℤ).ne')
  have hall := (Finset.sum_eq_sum_iff_of_le hpos).mp (by rw [hsum]; simp [hcard])
  have hw' := hall ⟨w.asIdeal, w.isPrime, liesOver_span_of_natCast_mem' l w.asIdeal hw⟩ (Finset.mem_univ _)
  exact mul_eq_one.mp hw'.symm

end K

section FE

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem locDeg_one_below (l : ℕ) [hl : Fact l.Prime]
    (h : {w : HeightOneSpectrum (𝓞 E) | ((l : ℕ) : 𝓞 E) ∈ w.asIdeal}.ncard = Module.finrank ℚ E)
    (p : HeightOneSpectrum (𝓞 F)) (hp : ((l : ℕ) : 𝓞 F) ∈ p.asIdeal) :
    p.asIdeal.ramificationIdx ℤ = 1 ∧ p.asIdeal.inertiaDeg ℤ = 1 := by
  haveI := p.isPrime
  obtain ⟨Q, -, hQ, hc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := 𝓞 E) p.asIdeal ⊥
    (by rw [Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective _ _)]; exact bot_le)
  haveI := hQ
  haveI : Q.LiesOver p.asIdeal := ⟨hc.symm⟩
  have hQ0 : Q ≠ ⊥ := by
    intro hb
    apply p.ne_bot
    rw [← hc, hb, Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective _ _)]
  have hw : ((l : ℕ) : 𝓞 E) ∈ Q := by
    rw [← hc] at hp
    simpa using Ideal.mem_comap.mp hp
  obtain ⟨he, hf⟩ := locDeg_one (K := E) l h ⟨Q, hQ, hQ0⟩ hw
  have he' := Ideal.ramificationIdx_tower (R := ℤ) p.asIdeal Q
  have hf' := Ideal.inertiaDeg_tower (R := ℤ) p.asIdeal Q
  exact ⟨(mul_eq_one.mp (he'.symm.trans he)).1, (mul_eq_one.mp (hf'.symm.trans hf)).1⟩

end FE

section Arith

variable {F : Type} [Field F] [NumberField F]

theorem arith_of_loc (l : ℕ) [hl : Fact l.Prime] (p : HeightOneSpectrum (𝓞 F))
    (hp : ((l : ℕ) : 𝓞 F) ∈ p.asIdeal) (he : p.asIdeal.ramificationIdx ℤ = 1)
    (hf : p.asIdeal.inertiaDeg ℤ = 1) :
    Nat.card (𝓞 F ⧸ p.asIdeal) = l ∧ ((l : ℕ) : 𝓞 F) ∉ p.asIdeal ^ 2 := by
  have hmaxl := Int.ideal_span_isMaximal_of_prime l
  haveI := p.isMaximal
  have hunder : Ideal.span {((l : ℕ) : ℤ)} = p.asIdeal.under ℤ := by
    refine hmaxl.eq_of_le (Ideal.IsPrime.ne_top (Ideal.IsPrime.under ℤ p.asIdeal)) ?_
    rw [Ideal.span_le, Set.singleton_subset_iff]
    show _ ∈ Ideal.comap (algebraMap ℤ (𝓞 F)) p.asIdeal
    rw [Ideal.mem_comap]
    simpa using hp
  haveI : p.asIdeal.LiesOver (Ideal.span {((l : ℕ) : ℤ)}) := ⟨hunder⟩
  constructor
  · have h := Ideal.cardQuot_pow_inertiaDeg (Ideal.span {((l : ℕ) : ℤ)}) p.asIdeal
    rw [hf, pow_one, Submodule.cardQuot_apply, Submodule.cardQuot_apply] at h
    rw [← h, Nat.card_congr (Int.quotientSpanNatEquivZMod l).toEquiv, Nat.card_zmod]
  · have hne : Ideal.span {((l : ℕ) : ℤ)} ≠ ⊥ := by
      rw [Ne, Ideal.span_singleton_eq_bot]
      exact_mod_cast hl.out.ne_zero
    have h1 : (Ideal.span {((l : ℕ) : ℤ)}).ramificationIdx' p.asIdeal = 1 := by
      rw [Ideal.ramificationIdx'_eq_ramificationIdx _ _ hne]
      exact he
    intro hmem
    have hle : Ideal.map (algebraMap ℤ (𝓞 F)) (Ideal.span {((l : ℕ) : ℤ)}) ≤ p.asIdeal ^ 2 := by
      rw [Ideal.map_span, Set.image_singleton, Ideal.span_le, Set.singleton_subset_iff]
      simpa using hmem
    unfold Ideal.ramificationIdx' at h1
    have hbdd : BddAbove {n | Ideal.map (algebraMap ℤ (𝓞 F)) (Ideal.span {((l : ℕ) : ℤ)}) ≤ p.asIdeal ^ n} := by
      by_contra hb
      rw [Nat.sSup_of_not_bddAbove hb] at h1
      exact zero_ne_one h1
    have h2 := le_csSup hbdd hle
    omega

end Arith

end Formalism.L2.SG.Pf.NcVal.VolUAr
