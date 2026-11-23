import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.Transported
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DepthZeroLabelsOfLabelLaws
import GroundTheory.GlobalFields.SemilocalAlgebras.Finite
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EqZeroOfForallLeExp

open NumberField IsDedekindDomain Formalism.BasicNotions GroundTheory.Global.SemiLocal

private theorem natGen_dvd_iff (x : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ) :
    Rat.HeightOneSpectrum.natGenerator x ∣ n ↔ ((n : ℕ) : 𝓞 ℚ) ∈ x.asIdeal := by
  rw [Rat.HeightOneSpectrum.natGenerator_dvd_iff,
    ← map_natCast (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) n, Ideal.apply_mem_of_equiv_iff]

private theorem mem_iff_eq (P : Nat.Primes) (x : HeightOneSpectrum (𝓞 ℚ)) :
    (((P : ℕ) : ℕ) : 𝓞 ℚ) ∈ x.asIdeal ↔ x = (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm P := by
  rw [Equiv.eq_symm_apply, ← natGen_dvd_iff]
  constructor
  · intro h
    apply Subtype.ext
    exact (Nat.prime_dvd_prime_iff_eq (Rat.HeightOneSpectrum.prime_natGenerator x) P.2).1 h
  · intro h
    rw [← h]
    exact dvd_refl _

theorem UpperTheory.exists_continuous_ringEquiv_padic_of_totally_split :
    ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (p : ℕ) [Fact p.Prime], w ∈ placesOver E p → (placesOver E p).ncard = Module.finrank ℚ E → ∃ i : ℚ_[p] ≃+* w.adicCompletion E, Continuous i := by
  intro E _ _ w p hp hw hcard
  let P : Nat.Primes := ⟨p, hp.out⟩
  let v : HeightOneSpectrum (𝓞 ℚ) := (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm P
  have hpv : ((p : ℕ) : 𝓞 ℚ) ∈ v.asIdeal := (mem_iff_eq P v).2 rfl
  have hlies : ∀ u : HeightOneSpectrum (𝓞 E), u ∈ placesOver E p ↔ u.asIdeal.LiesOver v.asIdeal := by
    intro u
    show ((p : ℕ) : 𝓞 E) ∈ u.asIdeal ↔ _
    rw [Ideal.liesOver_iff]
    constructor
    · intro hu
      have hmem : ((p : ℕ) : 𝓞 ℚ) ∈ u.asIdeal.under (𝓞 ℚ) := by
        rw [Ideal.under, Ideal.mem_comap, map_natCast]
        exact hu
      let q : HeightOneSpectrum (𝓞 ℚ) :=
        { asIdeal := u.asIdeal.under (𝓞 ℚ)
          isPrime := inferInstance
          ne_bot := by
            intro h
            rw [h, Ideal.mem_bot] at hmem
            exact hp.out.ne_zero (by exact_mod_cast hmem) }
      have hq : q = v := (mem_iff_eq P q).1 hmem
      rw [← hq]
    · intro h
      rw [h, Ideal.under, Ideal.mem_comap, map_natCast] at hpv
      exact hpv
  haveI : w.asIdeal.LiesOver v.asIdeal := (hlies w).1 hw
  have hcardS : Fintype.card (PlacesOver E v) = Module.finrank ℚ E := by
    rw [← hcard, ← Nat.card_coe_set_eq, ← Nat.card_eq_fintype_card]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun u => (hlies u).symm)
  have hone : ∀ u : PlacesOver E v,
      (u : HeightOneSpectrum (𝓞 E)).asIdeal.ramificationIdx (𝓞 ℚ) *
        (u : HeightOneSpectrum (𝓞 E)).asIdeal.inertiaDeg (𝓞 ℚ) = 1 := by
    have hsum := sum_ramificationIdx_mul_inertiaDeg (K := ℚ) E v
    intro u
    have hpos : ∀ u' : PlacesOver E v, 1 ≤
        (u' : HeightOneSpectrum (𝓞 E)).asIdeal.ramificationIdx (𝓞 ℚ) *
          (u' : HeightOneSpectrum (𝓞 E)).asIdeal.inertiaDeg (𝓞 ℚ) := fun u' =>
      Nat.mul_pos (Ideal.ramificationIdx_pos _ _) (Ideal.inertiaDeg_pos _ _)
    by_contra hne
    have hlt := Finset.sum_lt_sum (s := Finset.univ) (f := fun _ : PlacesOver E v => 1)
      (fun u' _ => hpos u') ⟨u, Finset.mem_univ _, lt_of_le_of_ne (hpos u) (Ne.symm hne)⟩
    rw [hsum, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one, hcardS] at hlt
    exact lt_irrefl _ hlt
  have hrank : Module.finrank (v.adicCompletion ℚ) (w.adicCompletion E) = 1 := by
    rw [finrank_eq_ramificationIdx_mul_inertiaDeg]
    exact hone ⟨w, inferInstance⟩
  have hsurj : Function.Surjective (completionMap v w) :=
    Algebra.surjective_algebraMap_iff.2 (Subalgebra.bot_eq_top_of_finrank_eq_one hrank).symm
  refine ⟨(Padic.adicCompletionEquiv (𝓞 ℚ) P).toRingEquiv.trans
    (RingEquiv.ofBijective (completionMap v w) ⟨(completionMap v w).injective, hsurj⟩), ?_⟩
  exact (continuous_completionMap v w).comp (Padic.adicCompletionEquiv (𝓞 ℚ) P).continuous
