import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

namespace GlobalTheory.SplitFullyNorm

theorem exists_prime_absNorm_eq_of_splitsFully (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (W : HeightOneSpectrum (𝓞 E)) (h : SplitsFully E (W.under (𝓞 F))) :
    ∃ p : ℕ, p.Prime ∧ Ideal.absNorm W.asIdeal = p ∧ (p : 𝓞 E) ∉ W.asIdeal ^ 2 := by
  classical

  set P : Ideal ℤ := W.asIdeal.under ℤ with hPdef
  have hP0 : P ≠ ⊥ := mt Ideal.eq_bot_of_comap_eq_bot W.ne_bot
  haveI hPprime : P.IsPrime := Ideal.IsPrime.under ℤ W.asIdeal
  haveI hPmax : P.IsMaximal := hPprime.isMaximal hP0

  have hunder : (W.under (𝓞 F)).asIdeal.under ℤ = P := by
    change (W.asIdeal.under (𝓞 F)).under ℤ = W.asIdeal.under ℤ
    exact Ideal.under_under _
  have hcard : (P.primesOver (𝓞 E)).ncard = Module.finrank ℚ E := by
    have h' := h
    unfold SplitsFully at h'
    rwa [hunder] at h'

  have hsum := Ideal.sum_ramification_inertia_eq_finrank P (𝓞 E)
  rw [NumberField.RingOfIntegers.rank] at hsum

  have hone : ∀ q : P.primesOver (𝓞 E), q.1.ramificationIdx ℤ * q.1.inertiaDeg ℤ = 1 := by
    intro q
    haveI : q.1.IsPrime := q.2.1
    have hpos := Nat.mul_pos (Ideal.ramificationIdx_pos q.1 ℤ) (Ideal.inertiaDeg_pos q.1 ℤ)
    by_contra hne
    have hlt : ∑ _r : P.primesOver (𝓞 E), (1 : ℕ) <
        ∑ r : P.primesOver (𝓞 E), r.1.ramificationIdx ℤ * r.1.inertiaDeg ℤ := by
      apply Finset.sum_lt_sum
      · intro r _
        haveI : r.1.IsPrime := r.2.1
        exact Nat.mul_pos (Ideal.ramificationIdx_pos r.1 ℤ) (Ideal.inertiaDeg_pos r.1 ℤ)
      · exact ⟨q, Finset.mem_univ _, by omega⟩
    rw [hsum, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one, Fintype.card_eq_nat_card,
      Nat.card_coe_set_eq, hcard] at hlt
    exact lt_irrefl _ hlt
  have hWmem : W.asIdeal ∈ P.primesOver (𝓞 E) := ⟨W.isPrime, ⟨rfl⟩⟩
  have hw := hone ⟨W.asIdeal, hWmem⟩
  have he : W.asIdeal.ramificationIdx ℤ = 1 := Nat.eq_one_of_mul_eq_one_right hw
  have hf : W.asIdeal.inertiaDeg ℤ = 1 := Nat.eq_one_of_mul_eq_one_left hw

  set n : ℕ := (Submodule.IsPrincipal.generator P).natAbs with hn
  have hspan : Ideal.span {((n : ℕ) : ℤ)} = P := by
    rw [hn, Int.span_natAbs, Ideal.span_singleton_generator]
  have hn0 : ((n : ℕ) : ℤ) ≠ 0 := by
    intro h0
    apply hP0
    rw [← hspan, h0, Ideal.span_singleton_eq_bot]
  have hnprime : n.Prime := by
    rw [Nat.prime_iff_prime_int, ← Ideal.span_singleton_prime hn0, hspan]
    exact hPprime
  haveI : W.asIdeal.LiesOver (Ideal.span {((n : ℕ) : ℤ)}) := ⟨by rw [hspan]⟩
  refine ⟨n, hnprime, ?_, ?_⟩
  ·
    rw [← Ideal.pow_inertiaDeg n W.asIdeal, hf, pow_one]
  ·
    intro hmem
    have hmap0 : P.map (algebraMap ℤ (𝓞 E)) ≠ ⊥ := Ideal.map_ne_bot_of_ne_bot hP0
    have hle : P.map (algebraMap ℤ (𝓞 E)) ≤ W.asIdeal ^ 2 := by
      rw [← hspan, Ideal.map_span, Set.image_singleton, Ideal.span_le, Set.singleton_subset_iff]
      simpa using hmem
    have hdvd : W.asIdeal ^ 2 ∣ P.map (algebraMap ℤ (𝓞 E)) := Ideal.dvd_iff_le.mpr hle
    have hfin : FiniteMultiplicity W.asIdeal (P.map (algebraMap ℤ (𝓞 E))) :=
      FiniteMultiplicity.of_not_isUnit (by rw [Ideal.isUnit_iff]; exact W.isPrime.ne_top) hmap0
    have h2 := hfin.le_multiplicity_of_pow_dvd hdvd
    rw [← Ideal.IsDedekindDomain.ramificationIdx_eq_multiplicity P W.asIdeal hmap0, he] at h2
    omega

end GlobalTheory.SplitFullyNorm
