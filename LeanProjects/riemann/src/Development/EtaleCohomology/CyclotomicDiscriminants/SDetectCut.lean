import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LemmaKOfSteps
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChebotarevDegreeOne

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual UpperTheory.V.ZK

namespace LateralTheory.Q.SDetectCut

theorem root_eq_one {R : Type} [CommRing R] [IsDomain R] (P : Ideal R) (q : ℕ) (η : R) (hη : η ^ q = 1)
    (h1 : η - 1 ∈ P) (hq : (q : R) ∉ P) : η = 1 := by
  by_contra hne
  apply hq
  have h0 : ∑ i ∈ Finset.range q, η ^ i = 0 := by
    have := mul_geom_sum η q
    rw [hη, sub_self] at this
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hne)
  have h2 : Ideal.Quotient.mk P η = 1 := by
    rw [← map_one (Ideal.Quotient.mk P), Ideal.Quotient.eq]
    exact h1
  have h3 := congrArg (Ideal.Quotient.mk P) h0
  simp only [map_sum, map_pow, h2, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one,
    map_zero] at h3
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  exact h3

theorem surj_of_prime {A k : Type} [CommRing A] [CommRing k] (f : A →+* k) (hp : (Nat.card k).Prime) :
    Function.Surjective f := by
  intro y
  have : Fact (Nat.card k).Prime := ⟨hp⟩
  have : Finite k := Nat.finite_of_card_ne_zero hp.ne_zero
  have : Nontrivial k := Finite.one_lt_card_iff_nontrivial.1 hp.one_lt
  obtain ⟨n, hn⟩ := mem_zmultiples_of_prime_card (G := k) (p := Nat.card k) rfl (g := 1) (g' := y) one_ne_zero
  exact ⟨n, by simpa using hn⟩

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]

omit [NumberField F] in
theorem val_le (B : ValuationSubring Ω) (x : 𝓞 F) : B.valuation (algebraMap F Ω (x : F)) ≤ 1 := by
  have hz : IsIntegral ℤ (algebraMap F Ω (x : F)) := x.isIntegral_coe.map (algebraMap F Ω).toIntAlgHom
  exact (Valuation.integer.integers B.valuation).mem_of_integral hz.tower_top

omit [NumberField F] in

theorem frob_fix {v : HeightOneSpectrum (𝓞 F)} {B : ValuationSubring Ω} (hB : IsPlaceOver B v) {N : ℕ} (hN : N ≠ 0)
    {σ : G F Ω} (hσ : IsFrob B N σ) {q : ℕ} (hq0 : q ≠ 0) (hq : (q : 𝓞 F) ∉ v.asIdeal) {ζ : 𝓞 F}
    (hζ : IsPrimitiveRoot ζ q) {β : F} {x : Ω} (hx : x ^ q = algebraMap F Ω β) {a b t : 𝓞 F}
    (hb : b ∉ v.asIdeal) (ht : t ∉ v.asIdeal) (hab : β * b = a) (hc : a - t ^ q * b ∈ v.asIdeal) : σ x = x := by
  have : NeZero q := ⟨hq0⟩
  let ι : 𝓞 F →+* Ω := (algebraMap F Ω).comp (algebraMap (𝓞 F) F)
  have hι : ∀ y : 𝓞 F, ι y = algebraMap F Ω (y : F) := fun _ => rfl
  have hinj : Function.Injective ι := (algebraMap F Ω).injective.comp (RingOfIntegers.coe_injective)
  have hone : ∀ y : 𝓞 F, y ∉ v.asIdeal → B.valuation (ι y) = 1 := fun y hy =>
    le_antisymm (val_le B y) (not_lt.1 fun h => hy ((hB y).1 h))
  have hζ' : IsPrimitiveRoot (ι ζ) q := hζ.map_of_injective hinj
  have h1 : B.valuation (x ^ q - ι t ^ q) < 1 := by
    have e : (x ^ q - ι t ^ q) * ι b = ι (a - t ^ q * b) := by
      rw [hx, map_sub, map_mul, map_pow, sub_mul, hι a, hι b, ← hab, map_mul]
    have := (hB _).2 hc
    rw [← hι, ← e, map_mul, hone b hb, mul_one] at this
    exact this
  obtain ⟨i, hi⟩ : ∃ i : ℕ, B.valuation (x - ι (ζ ^ i * t)) < 1 := by
    by_contra! h
    have e := congrArg (Polynomial.eval x) (X_pow_sub_C_eq_prod hζ' (Nat.pos_of_ne_zero hq0) (rfl : ι t ^ q = ι t ^ q))
    simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C,
      Polynomial.eval_prod] at e
    rw [e, map_prod] at h1
    refine absurd h1 (not_lt.2 (Finset.one_le_prod' fun i _ => ?_))
    have := h i
    rwa [map_mul, map_pow] at this
  set c := ζ ^ i * t with hcdef
  have hcv : c ∉ v.asIdeal := fun h =>
    ht ((v.isPrime.mem_or_mem h).resolve_left fun h' =>
      v.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h' ((hζ.isUnit hq0).pow i)))
  have hxv : B.valuation x = 1 := by
    rw [← hone c hcv]
    exact Valuation.map_eq_of_sub_lt _ (by rw [hone c hcv]; exact hi)
  have h2 : B.valuation (σ (x - ι c)) < 1 := by
    have e : σ (x - ι c) = (σ (x - ι c) - (x - ι c) ^ N) + (x - ι c) ^ N := by ring
    rw [e]
    refine Valuation.map_add_lt _ (hσ.2 _ hi.le) ?_
    rw [map_pow]
    exact pow_lt_one' hi hN
  have h3 : B.valuation (σ x - x) < 1 := by
    have e : σ x - x = σ (x - ι c) - (x - ι c) := by
      rw [map_sub, hι, AlgEquiv.commutes]; ring
    rw [e]
    exact Valuation.map_sub_lt _ h2 hi
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hxv
  have h4 : (σ x / x) ^ q = 1 := by
    rw [div_pow, ← map_pow, hx, AlgEquiv.commutes, ← hx, div_self (pow_ne_zero _ hx0)]
  obtain ⟨j, -, hj⟩ := hζ'.eq_pow_of_pow_eq_one h4
  have h5 : σ x = ι (ζ ^ j) * x := by rw [map_pow, hj, div_mul_cancel₀ _ hx0]
  have h6 : ζ ^ j - 1 ∈ v.asIdeal := by
    rw [← hB, ← hι]
    have e : σ x - x = ι (ζ ^ j - 1) * x := by rw [h5, map_sub, map_one]; ring
    rwa [e, map_mul, hxv, mul_one] at h3
  have h7 : ζ ^ j = 1 := root_eq_one v.asIdeal q _ (by rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]) h6 hq
  rw [h5, h7, map_one, one_mul]

theorem goal : SDetect := by
  intro L F _ _ _ _ _ l ν hl ζ hζ β b hb H
  have hq0 : l ^ ν ≠ 0 := pow_ne_zero _ hl.ne_zero
  generalize l ^ ν = q at *
  let Ω := AlgebraicClosure F
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap F Ω (β : F)) (Nat.pos_of_ne_zero hq0)
  have hS : {v : HeightOneSpectrum (𝓞 F) | b * (q : 𝓞 F) ∈ v.asIdeal}.Finite := by
    simp_rw [← Ideal.dvd_span_singleton]
    exact Ideal.finite_factors (by simp [hb, hq0])
  have : IsGalois F Ω := {}
  have hfix : ∀ g : Ω ≃ₐ[F] Ω, g x = x := by
    intro g
    have hV : IsOpen {σ : G F Ω | σ x = g x} := by
      have h1 : IsOpen (MulAction.stabilizer (Ω ≃ₐ[F] Ω) x : Set (Ω ≃ₐ[F] Ω)) := stabilizer_isOpen_of_isIntegral x
      have h2 := h1.preimage (continuous_const_mul g⁻¹)
      convert h2 using 1
      ext σ
      simp only [Set.mem_ofPred_eq, Set.mem_preimage, SetLike.mem_coe, MulAction.mem_stabilizer_iff, mul_smul,
        inv_smul_eq_iff]
      rfl
    obtain ⟨σ, hσV, v, hv, hd, B, hB, hσ⟩ :=
      (GlobalTheory.Published.ChebotarevDegreeOne.dense (F := F) (Ω := Ω) GlobalTheory.Published.chebotarevDegreeOne'
        hS).inter_open_nonempty _ hV ⟨g, rfl⟩
    have hp : (Nat.card (𝓞 F ⧸ v.asIdeal)).Prime := by
      have := ((GlobalTheory.absNorm_prime_iff_inertiaDeg_eq_one_and_finite_ramified F).1 v).2 hd
      rwa [Ideal.absNorm_apply, Submodule.cardQuot_apply] at this
    have := v.isMaximal
    obtain ⟨s, a, b', hb', hab, hr⟩ := H v (fun h => hv (Ideal.mul_mem_right _ _ h)) (surj_of_prime _ hp)
    let := Ideal.Quotient.field v.asIdeal
    obtain ⟨t, ht⟩ := Ideal.Quotient.mk_surjective (s : 𝓞 F ⧸ v.asIdeal)
    rw [← hσV]
    refine frob_fix hB hp.ne_zero hσ hq0 (fun h => hv (Ideal.mul_mem_left _ _ h))
      (IsPrimitiveRoot.coe_units_iff.2 hζ) hx (a := a) (b := b') (t := t)
      (fun h => hb' (Ideal.Quotient.eq_zero_iff_mem.2 h))
      (fun h => s.ne_zero (ht ▸ Ideal.Quotient.eq_zero_iff_mem.2 h)) hab ?_
    rw [← Ideal.Quotient.eq, map_mul, map_pow, ht, hr, Units.val_pow_eq_pow_val]
  obtain ⟨δ, hδ⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed x).2 hfix
  have hd : (β : F) = δ ^ q := (algebraMap F Ω).injective (by rw [map_pow, hδ, hx])
  have h0 : δ ≠ 0 := by
    rintro rfl
    exact β.ne_zero (by rw [hd, zero_pow hq0])
  exact ⟨Units.mk0 δ h0, Units.ext (by simpa using hd)⟩

end LateralTheory.Q.SDetectCut
