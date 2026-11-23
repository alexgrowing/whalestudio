import Mathlib
import Formalism.SatakeDualWeyl.Statement
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SatGramLoc

noncomputable section

open NumberField IsDedekindDomain
open scoped TensorProduct

namespace Formalism.L2.SG.Pf.SatGramLoc

section Deg

variable {K : Type} [Field K] [NumberField K]

theorem liesOver_natCast (p : ℕ) (hp : p.Prime)
    (v : HeightOneSpectrum (𝓞 K)) (hv : ((p : ℕ) : 𝓞 K) ∈ v.asIdeal) :
    v.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) := by
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible hpZ.irreducible
  have hne : Ideal.comap (algebraMap ℤ (𝓞 K)) v.asIdeal ≠ ⊤ := Ideal.comap_ne_top _ v.isPrime.ne_top
  have hle : Ideal.span {(p : ℤ)} ≤ Ideal.comap (algebraMap ℤ (𝓞 K)) v.asIdeal := by
    rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap]
    simpa using hv
  constructor
  exact hmax.eq_of_le hne hle

theorem image_places_primesOver (p : ℕ) (hp : p.Prime) :
    (fun v : HeightOneSpectrum (𝓞 K) => v.asIdeal) '' {v | ((p : ℕ) : 𝓞 K) ∈ v.asIdeal} =
      (Ideal.span {(p : ℤ)}).primesOver (𝓞 K) := by
  ext P
  simp only [Set.mem_image, Set.mem_setOf_eq, Ideal.primesOver]
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨v.isPrime, liesOver_natCast p hp v hv⟩
  · rintro ⟨hP, hPo⟩
    have h' : (p : ℤ) ∈ Ideal.span {(p : ℤ)} := Ideal.subset_span rfl
    rw [hPo.over] at h'
    have h'' : algebraMap ℤ (𝓞 K) (p : ℤ) ∈ P := h'
    have hmem : ((p : ℕ) : 𝓞 K) ∈ P := by simpa using h''
    have hne : P ≠ ⊥ := by
      intro h
      rw [h, Ideal.mem_bot] at hmem
      exact hp.ne_zero (by exact_mod_cast hmem)
    exact ⟨⟨P, hP, hne⟩, hmem, rfl⟩

theorem ram_inertia_split (p : ℕ) (hp : p.Prime)
    (hs : {v : HeightOneSpectrum (𝓞 K) | ((p : ℕ) : 𝓞 K) ∈ v.asIdeal}.ncard = Module.finrank ℚ K)
    (v : HeightOneSpectrum (𝓞 K)) (hv : ((p : ℕ) : 𝓞 K) ∈ v.asIdeal) :
    v.asIdeal.ramificationIdx ℤ = 1 ∧ v.asIdeal.inertiaDeg ℤ = 1 := by
  classical
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
  have hpI : (Ideal.span {(p : ℤ)}).IsPrime := (Ideal.span_singleton_prime hpZ.ne_zero).2 hpZ
  have hpM : (Ideal.span {(p : ℤ)}).IsMaximal :=
    hpI.isMaximal (by rw [Ne, Ideal.span_singleton_eq_bot]; exact hpZ.ne_zero)
  have hsum := Ideal.sum_ramification_inertia_eq_finrank (Ideal.span {(p : ℤ)}) (𝓞 K)
  rw [RingOfIntegers.rank, ← hs, ← Set.ncard_image_of_injective _
    (fun v w h => HeightOneSpectrum.ext h), image_places_primesOver p hp,
    ← Nat.card_coe_set_eq, Nat.card_eq_fintype_card, Fintype.card_eq_sum_ones] at hsum
  have hle : ∀ q : (Ideal.span {(p : ℤ)}).primesOver (𝓞 K),
      1 ≤ q.1.ramificationIdx ℤ * q.1.inertiaDeg ℤ := by
    rintro ⟨q, hq, hql⟩
    exact Nat.mul_pos (Ideal.ramificationIdx_pos q ℤ) (Ideal.inertiaDeg_pos q ℤ)
  have hall := (Finset.sum_eq_sum_iff_of_le (fun q _ => hle q)).1 hsum.symm
    ⟨v.asIdeal, v.isPrime, liesOver_natCast p hp v hv⟩ (Finset.mem_univ _)
  exact ⟨Nat.dvd_one.1 ⟨_, hall⟩, Nat.dvd_one.1 ⟨_, hall.trans (mul_comm _ _)⟩⟩

theorem card_quot_split (p : ℕ) (hp : p.Prime)
    (hs : {v : HeightOneSpectrum (𝓞 K) | ((p : ℕ) : 𝓞 K) ∈ v.asIdeal}.ncard = Module.finrank ℚ K)
    (v : HeightOneSpectrum (𝓞 K)) (hv : ((p : ℕ) : 𝓞 K) ∈ v.asIdeal) :
    Nat.card (𝓞 K ⧸ v.asIdeal) = p := by
  haveI := liesOver_natCast p hp v hv
  have h := Ideal.absNorm_eq_pow_inertiaDeg' v.asIdeal hp
  have hf := (ram_inertia_split p hp hs v hv).2
  have h2 : (Ideal.span {((p : ℕ) : ℤ)}).inertiaDeg' v.asIdeal = 1 := by
    haveI : (Ideal.span {((p : ℕ) : ℤ)}).IsMaximal :=
      PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible
    haveI : v.asIdeal.IsMaximal := v.isMaximal
    rw [Ideal.inertiaDeg'_eq_inertiaDeg, hf]
  rw [h2, pow_one] at h
  rw [← h, Ideal.absNorm_apply, Submodule.cardQuot_apply]

theorem intValuation_split (p : ℕ) (hp : p.Prime)
    (hs : {v : HeightOneSpectrum (𝓞 K) | ((p : ℕ) : 𝓞 K) ∈ v.asIdeal}.ncard = Module.finrank ℚ K)
    (v : HeightOneSpectrum (𝓞 K)) (hv : ((p : ℕ) : 𝓞 K) ∈ v.asIdeal) :
    v.intValuation ((p : ℕ) : 𝓞 K) = WithZero.exp (-1 : ℤ) := by
  have := v.isPrime
  have hr : ((p : ℕ) : 𝓞 K) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have hmap : (Ideal.span {((p : ℕ) : ℤ)}).map (algebraMap ℤ (𝓞 K)) = Ideal.span {((p : ℕ) : 𝓞 K)} := by
    rw [Ideal.map_span, Set.image_singleton]
    simp
  have hne : (Ideal.span {((p : ℕ) : ℤ)}).map (algebraMap ℤ (𝓞 K)) ≠ ⊥ := by
    rw [hmap, Ne, Ideal.span_singleton_eq_bot]; exact hr
  have := liesOver_natCast p hp v hv
  have he := Ideal.IsDedekindDomain.ramificationIdx_eq_multiplicity (Ideal.span {((p : ℕ) : ℤ)})
    v.asIdeal hne
  rw [hmap, (ram_inertia_split p hp hs v hv).1] at he
  rw [v.intValuation_eq_exp_neg_multiplicity hr, ← he]
  rfl

end Deg

theorem ram_inertia_sub {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (p : ℕ) (hp : p.Prime)
    (hs : {w : HeightOneSpectrum (𝓞 E) | ((p : ℕ) : 𝓞 E) ∈ w.asIdeal}.ncard = Module.finrank ℚ E)
    (v : HeightOneSpectrum (𝓞 F)) (hv : ((p : ℕ) : 𝓞 F) ∈ v.asIdeal) :
    v.asIdeal.ramificationIdx ℤ = 1 ∧ v.asIdeal.inertiaDeg ℤ = 1 := by
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
  have hvp := v.isPrime
  have hvl : v.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) := liesOver_natCast p hp v hv
  obtain ⟨⟨P, hPp, hPl⟩⟩ : Nonempty (v.asIdeal.primesOver (𝓞 E)) := inferInstance
  have hPZ : P.LiesOver (Ideal.span {(p : ℤ)}) := Ideal.LiesOver.trans P v.asIdeal _
  have hP0 : P ≠ ⊥ := by
    rintro rfl
    have h0 : Ideal.span {(p : ℤ)} = ⊥ := by
      rw [hPZ.over]; exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective ℤ (𝓞 E))
    exact hpZ.ne_zero (Ideal.span_singleton_eq_bot.1 h0)
  have hPmem : ((p : ℕ) : 𝓞 E) ∈ P := by
    have : (p : ℤ) ∈ P.under ℤ := by rw [← hPZ.over]; exact Ideal.mem_span_singleton_self _
    simpa using this
  obtain ⟨he, hf⟩ := ram_inertia_split (K := E) p hp hs ⟨P, hPp, hP0⟩ hPmem
  change P.ramificationIdx ℤ = 1 at he
  change P.inertiaDeg ℤ = 1 at hf
  rw [Ideal.ramificationIdx_tower (R := ℤ) v.asIdeal P] at he
  rw [Ideal.inertiaDeg_tower (R := ℤ) v.asIdeal P] at hf
  exact ⟨Nat.eq_one_of_mul_eq_one_right he, Nat.eq_one_of_mul_eq_one_right hf⟩

theorem split_sub {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (p : ℕ) (hp : p.Prime)
    (hs : {w : HeightOneSpectrum (𝓞 E) | ((p : ℕ) : 𝓞 E) ∈ w.asIdeal}.ncard = Module.finrank ℚ E) :
    {v : HeightOneSpectrum (𝓞 F) | ((p : ℕ) : 𝓞 F) ∈ v.asIdeal}.ncard = Module.finrank ℚ F := by
  classical
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
  have hpI : (Ideal.span {(p : ℤ)}).IsPrime := (Ideal.span_singleton_prime hpZ.ne_zero).2 hpZ
  have hpM : (Ideal.span {(p : ℤ)}).IsMaximal :=
    hpI.isMaximal (by rw [Ne, Ideal.span_singleton_eq_bot]; exact hpZ.ne_zero)
  have hsum := Ideal.sum_ramification_inertia_eq_finrank (Ideal.span {(p : ℤ)}) (𝓞 F)
  have hone : ∀ q : (Ideal.span {(p : ℤ)}).primesOver (𝓞 F),
      q.1.ramificationIdx ℤ * q.1.inertiaDeg ℤ = 1 := by
    rintro ⟨q, hq, hql⟩
    have hq0 : q ≠ ⊥ := by
      rintro rfl
      have h0 : Ideal.span {(p : ℤ)} = ⊥ := by
        rw [hql.over]; exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective ℤ (𝓞 F))
      exact hpZ.ne_zero (Ideal.span_singleton_eq_bot.1 h0)
    have hqmem : ((p : ℕ) : 𝓞 F) ∈ q := by
      have : (p : ℤ) ∈ q.under ℤ := by rw [← hql.over]; exact Ideal.mem_span_singleton_self _
      simpa using this
    obtain ⟨h1, h2⟩ := ram_inertia_sub (E := E) p hp hs ⟨q, hq, hq0⟩ hqmem
    change q.ramificationIdx ℤ * q.inertiaDeg ℤ = 1
    rw [h1, h2]
  simp only [hone, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one] at hsum
  rw [RingOfIntegers.rank] at hsum
  rw [← hsum, ← Set.ncard_image_of_injective _ (fun v w h => HeightOneSpectrum.ext h),
    image_places_primesOver p hp, ← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]

theorem split_prime_local_holds : SplitPrimeLoc := by
  intro F E _ _ _ _ _ p hp hs
  have hF := split_sub (F := F) (E := E) p hp hs
  refine ⟨fun v hv => ⟨card_quot_split p hp hF v hv, ?_⟩, hF⟩
  have h1 := intValuation_split p hp hF v hv
  first
  | exact h1
  | (rw [← h1, ← HeightOneSpectrum.valuation_of_algebraMap (K := F),
      ← HeightOneSpectrum.valuedAdicCompletion_eq_valuation']; congr 1; exact (map_natCast (algebraMap F (v.adicCompletion F)) p).symm)
  | (rw [← h1, ← HeightOneSpectrum.valuation_of_algebraMap (K := F),
      ← HeightOneSpectrum.valuedAdicCompletion_eq_valuation']; congr 1; simp; done)
  | (rw [← h1, ← HeightOneSpectrum.valuation_of_algebraMap (K := F),
      ← HeightOneSpectrum.valuedAdicCompletion_eq_valuation']; congr 1; norm_cast; done)
  | (rw [← h1, ← HeightOneSpectrum.valuation_of_algebraMap (K := F),
      ← HeightOneSpectrum.valuedAdicCompletion_eq_valuation']; simp; done)
  | (rw [← h1, ← HeightOneSpectrum.valuation_of_algebraMap (K := F),
      ← HeightOneSpectrum.valuedAdicCompletion_eq_valuation']; rfl)

end Formalism.L2.SG.Pf.SatGramLoc

end
