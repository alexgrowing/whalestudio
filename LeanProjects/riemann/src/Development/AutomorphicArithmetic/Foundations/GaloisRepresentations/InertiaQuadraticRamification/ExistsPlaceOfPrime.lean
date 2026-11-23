import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.InertSplitAlt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TameKummerInertiaSurjective
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSolvableCmExtensionSplitPlace
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.V.Published GlobalTheory.RealGal GlobalTheory.UnitaryBC
open UpperTheory.Gal.UnramifiedFromSplittingCriterion

private theorem exists_prime_val {Ω : Type} [Field Ω] (A : ValuationSubring Ω) :
    ∀ n : ℕ, n ≠ 0 → A.valuation (n : Ω) < 1 → ∃ r : ℕ, r.Prime ∧ r ∣ n ∧ A.valuation (r : Ω) < 1 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn hv
    have hn1 : n ≠ 1 := by
      rintro rfl
      simp at hv
    have hp := Nat.minFac_prime hn1
    obtain ⟨m, hm⟩ := Nat.minFac_dvd n
    by_cases h : A.valuation ((n.minFac : ℕ) : Ω) < 1
    · exact ⟨_, hp, Nat.minFac_dvd n, h⟩
    · have h1 : A.valuation ((n.minFac : ℕ) : Ω) = 1 :=
        le_antisymm (ReciprocityTheory.Gal.valuation_natCast_le_one A _) (not_lt.1 h)
      have hm0 : m ≠ 0 := by
        rintro rfl
        exact hn (by simpa using hm)
      have hlt : m < n := by
        have h2 := hp.two_le
        have h3 := Nat.pos_of_ne_zero hm0
        nlinarith [hm]
      have hvm : A.valuation (m : Ω) < 1 := by
        have e : A.valuation ((n : ℕ) : Ω) = A.valuation ((n.minFac : ℕ) : Ω) * A.valuation (m : Ω) := by
          rw [← map_mul, ← Nat.cast_mul, ← hm]
        rwa [e, h1, one_mul] at hv
      obtain ⟨r, hr, hrm, hrv⟩ := ih m hlt hm0 hvm
      exact ⟨r, hr, hrm.trans ⟨n.minFac, by rw [mul_comm]; exact hm⟩, hrv⟩

private theorem normV_pos' {F : Type} [Field F] [NumberField F] (t : HeightOneSpectrum (𝓞 F)) : 0 < normV t := by
  haveI : Finite (𝓞 F ⧸ t.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ t.ne_bot
  exact Nat.card_pos

private theorem normV_mem {F : Type} [Field F] [NumberField F] (t : HeightOneSpectrum (𝓞 F)) :
    ((normV t : ℕ) : 𝓞 F) ∈ t.asIdeal := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  simpa [normV, nsmul_eq_mul] using card_nsmul_eq_zero' (G := 𝓞 F ⧸ t.asIdeal) (x := 1)

private theorem exists_place_of_prime {K : Type} [Field K] [NumberField K] {q : ℕ} (hq : q.Prime) :
    ∃ u : HeightOneSpectrum (𝓞 K), ((q : ℕ) : 𝓞 K) ∈ u.asIdeal := by
  have hne : Ideal.span {((q : ℕ) : 𝓞 K)} ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]
    intro h
    have h2 := h.map (Algebra.norm ℤ (S := 𝓞 K))
    rw [show ((q : ℕ) : 𝓞 K) = algebraMap ℤ (𝓞 K) (q : ℤ) by simp, Algebra.norm_algebraMap,
      isUnit_pow_iff Module.finrank_pos.ne'] at h2
    exact (Nat.prime_iff_prime_int.1 hq).not_unit h2
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
  have hq0 : ((q : ℕ) : 𝓞 K) ≠ 0 := Nat.cast_ne_zero.2 hq.ne_zero
  have hmem := hle (Ideal.mem_span_singleton_self ((q : ℕ) : 𝓞 K))
  exact ⟨⟨M, hM.isPrime, fun h => hq0 (by rwa [h, Ideal.mem_bot] at hmem)⟩, hmem⟩

private theorem exists_moves {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    {q : ℕ} (hq : q.Prime) (h2 : 2 < q) (hB : ∀ w : HeightOneSpectrum (𝓞 K), ((q : ℕ) : 𝓞 K) ∉ w.asIdeal ^ 2)
    {x : Ω} (hx : x ^ 2 = ((q : ℕ) : Ω)) :
    ∃ (u : HeightOneSpectrum (𝓞 K)) (A : ValuationSubring Ω), ((q : ℕ) : 𝓞 K) ∈ u.asIdeal ∧ IsPlaceOver A u ∧
      ∃ σ ∈ Ine (F := K) A, σ x = -x := by
  obtain ⟨u, hu⟩ := exists_place_of_prime (K := K) hq
  obtain ⟨A, hA⟩ := ReciprocityTheory.Gal.exists_isPlaceOver Ω u
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨σ, hσ, h⟩ := GlobalTheory.TameKummerInertia.tame_kummer_surj K Ω A u hA q hu (hB u) 2 two_pos
    (fun hd => by have := Nat.le_of_dvd two_pos hd; omega) x (-1) hx (by norm_num)
  exact ⟨u, A, hu, hA, σ, hσ, by rw [h]; ring⟩

theorem UpperTheory.Gal.UnramifiedFromSplittingCriterion.quad0Ex :
    SqrtFix → MkQ → UnrLarge → Quad0Ex := by
  intro hS hM hU E Ω _ _ _ _ _ _ T hT
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  haveI : Algebra.IsAlgebraic E Ω := IsAlgClosure.isAlgebraic
  haveI : Algebra.IsAlgebraic ℚ Ω := Algebra.IsAlgebraic.trans ℚ E Ω
  obtain ⟨E', hfin, hE'⟩ : ∃ E' : IntermediateField ℚ Ω, FiniteDimensional ℚ E' ∧
      ∀ (j : E →+* Ω) (y : E), j y ∈ E' :=
    ⟨IntermediateField.normalClosure ℚ E Ω, inferInstance,
      fun j y => AlgHom.fieldRange_le_normalClosure j.toRatAlgHom ⟨y, rfl⟩⟩
  haveI : NumberField E' := { }
  haveI : IsAlgClosure E' Ω := ⟨inferInstance, Algebra.IsAlgebraic.tower_top (K := ℚ) _⟩
  obtain ⟨B1, hB1⟩ := hU E
  obtain ⟨B2, hB2⟩ := hU E'
  obtain ⟨c, hc⟩ : ∃ c : ℕ, c = ∏ t ∈ hT.toFinset, normV t := ⟨_, rfl⟩
  have hc0 : 0 < c := hc ▸ Finset.prod_pos fun t _ => normV_pos' t
  have hcd : ∀ t ∈ T, normV t ∣ c := fun t ht => hc ▸ Finset.dvd_prod_of_mem _ (hT.mem_toFinset.2 ht)
  obtain ⟨q, hq, hgt, hmod⟩ := Nat.exists_prime_gt_modEq_one (k := 8 * c) (max (max B1 B2) (max c 2)) (by omega)
  simp only [max_lt_iff] at hgt
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hgt
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq ((q : ℕ) : Ω) two_pos
  have hx0 : x ≠ 0 := by
    rintro rfl
    have : ((q : ℕ) : Ω) = 0 := by rw [← hx]; simp
    exact hq.ne_zero (Nat.cast_eq_zero.1 this)
  have hneg : -x ≠ x := fun h => hx0 (by
    have : (2 : Ω) * x = 0 := by linear_combination -h
    simpa using this)
  obtain ⟨u', A', _, _, σ', hσ', hσ'x⟩ := exists_moves (K := E') hq h4 (hB2 q hq h2) hx
  obtain ⟨u, A, huq, hA, τ, hτ, hτx⟩ := exists_moves (K := E) hq h4 (hB1 q hq h1) hx
  have hxZ : x ^ 2 = (((q : ℕ) : ℤ) : Ω) := by rw [hx]; simp
  obtain ⟨Q, hxQ, hspan, hfix⟩ := hM E Ω x (q : ℤ) hxZ ⟨τ, by rw [hτx]; exact hneg⟩
  have hfixT : ∀ (F : Type) [Field F] [NumberField F] [Algebra F Ω], ∀ t ∈ T, ∀ A : ValuationSubring Ω,
      IsPlaceOver A t → ∀ g ∈ Dec (F := F) A, g x = x := by
    intro F _ _ _ t ht A hA g hg
    have hv : A.valuation ((normV t : ℕ) : Ω) < 1 := by
      have := (hA _).2 (normV_mem t)
      simpa using this
    obtain ⟨r, hr, hrd, hrv⟩ := exists_prime_val A _ (normV_pos' t).ne' hv
    refine (hS F Ω A x q hxZ).1 r hr hrv ?_ g hg
    have h8 : 8 * r ∣ 8 * c := Nat.mul_dvd_mul_left 8 (hrd.trans (hcd t ht))
    exact (Int.natCast_dvd_natCast.2 h8).trans (Nat.modEq_iff_dvd.1 hmod.symm)
  have hs1 : ∀ (j : E →+* Ω) (y : E), σ'.toRingEquiv (j y) = j y := fun j y => by
    simpa using σ'.commutes (⟨j y, hE' j y⟩ : E')
  have huT : u ∉ T := by
    intro ht
    have hle : normV u ≤ c := Nat.le_of_dvd hc0 (hcd u ht)
    have hcop : Nat.Coprime q (normV u) :=
      (Nat.Prime.coprime_iff_not_dvd hq).2 fun hd => by
        have := Nat.le_of_dvd (normV_pos' u) hd
        omega
    obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 hcop
    have h1 : (a : 𝓞 E) * ((q : ℕ) : 𝓞 E) + (b : 𝓞 E) * ((normV u : ℕ) : 𝓞 E) = 1 := by
      exact_mod_cast congrArg (Int.cast : ℤ → 𝓞 E) hab
    have hmem : (1 : 𝓞 E) ∈ u.asIdeal := by
      rw [← h1]
      exact add_mem (Ideal.mul_mem_left _ _ huq) (Ideal.mul_mem_left _ _ (normV_mem u))
    exact (Ideal.ne_top_iff_one _).1 u.isPrime.ne_top hmem
  refine ⟨Q, ⟨⟨x, hxQ⟩, ⟨⟨q, hq.pos, ?_⟩, hspan, σ'.toRingEquiv, hs1, hσ'x⟩, ?_⟩, ?_, u, huT, A, hA, τ, hτ, ?_⟩
  · apply Subtype.ext
    simpa using hx
  · intro t ht A hA g hg
    exact hfixT _ t ht A hA g hg
  · intro t ht A hA g hg
    exact hfix E g (fun y => g.commutes y) (hfixT E t ht A hA g hg)
  · intro hf
    have := hf ⟨x, hxQ⟩
    exact hneg (hτx.symm.trans this)
