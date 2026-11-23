import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.UnrCharAtOf
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.V.Published
open UpperTheory.Gal.UnramifiedFromSplittingCriterion

private theorem chi_of_pow {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] {p : ℕ} [Fact p.Prime] {ζ : Ω}
    (hζ : IsPrimitiveRoot ζ p) (g : G F Ω) (k : ℕ) (h : g ζ = ζ ^ k) :
    ((hζ.autToPow F g : (ZMod p)ˣ) : ZMod p) = (k : ZMod p) := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have h1 := IsPrimitiveRoot.autToPow_spec F hζ g
  have h2 : ζ ^ (k % p) = ζ ^ k := by
    conv_lhs => rw [hζ.eq_orderOf]
    exact pow_mod_orderOf ζ k
  rw [h, ← h2] at h1
  have h3 := hζ.pow_inj (ZMod.val_lt _) (Nat.mod_lt _ hp) h1
  rw [← ZMod.natCast_mod k p, ← h3, ZMod.natCast_val, ZMod.cast_id', id]

private theorem chi_one {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] {p : ℕ} [Fact p.Prime] {ζ : Ω}
    (hζ : IsPrimitiveRoot ζ p) (g : G F Ω) (h : g ζ = ζ) : hζ.autToPow F g = 1 := by
  apply Units.ext
  rw [chi_of_pow hζ g 1 (by rw [pow_one, h]), Nat.cast_one, Units.val_one]

private theorem exists_prim {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    (p : ℕ) [Fact p.Prime] : ∃ ζ : Ω, IsPrimitiveRoot ζ p := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  haveI : NeZero ((p : ℕ) : Ω) := ⟨Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero⟩
  exact HasEnoughRootsOfUnity.exists_primitiveRoot Ω p

private theorem chi_conj {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] {p : ℕ} [Fact p.Prime] {ζ : Ω}
    (hζ : IsPrimitiveRoot ζ p) (j : Ω →+* ℂ) (c : G F Ω) (hc : ∀ x, j (c x) = starRingEnd ℂ (j x)) :
    hζ.autToPow F c = -1 := by
  have hp : p.Prime := Fact.out
  have hjζ : IsPrimitiveRoot (j ζ) p := hζ.map_of_injective j.injective
  have hn : ‖j ζ‖ = 1 := hjζ.norm'_eq_one hp.ne_zero
  have hne : j ζ ≠ 0 := hjζ.ne_zero hp.ne_zero
  have h1 : c ζ = ζ ^ (p - 1) := by
    apply j.injective
    rw [hc, ← Complex.inv_eq_conj hn, map_pow]
    apply inv_eq_of_mul_eq_one_right
    rw [← pow_succ', Nat.sub_add_cancel hp.one_le, hjζ.pow_eq_one]
  apply Units.ext
  rw [chi_of_pow hζ c _ h1, Nat.cast_sub hp.one_le, ZMod.natCast_self, Nat.cast_one, zero_sub, Units.val_neg, Units.val_one]

private theorem good_ker {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {p : ℕ}
    [Fact p.Prime] {ζ : Ω} (hζ : IsPrimitiveRoot ζ p) (lam : (ZMod p)ˣ →* ℂˣ) (h1 : lam (-1) = 1) :
    Good (lam.comp (hζ.autToPow F)).ker := by
  haveI : Algebra.IsIntegral F Ω := (IsAlgClosure.isAlgebraic (R := F) (K := Ω)).isIntegral
  refine ⟨?_, Abelianization.commutator_subset_ker _, ?_⟩
  · refine Subgroup.isOpen_mono (H₁ := MulAction.stabilizer (G F Ω) ζ) ?_
      (stabilizer_isOpen_of_isIntegral (K := F) ζ)
    intro g hg
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, chi_one hζ g hg, map_one]
  · intro j c hc
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, chi_conj hζ j c hc, h1]

private theorem normV_mem {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    1 < normV v ∧ ((normV v : ℕ) : 𝓞 F) ∈ v.asIdeal := by
  have hc : normV v = Ideal.absNorm v.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]; rfl
  have hmem : ((normV v : ℕ) : 𝓞 F) ∈ v.asIdeal := by
    rw [hc]; exact Ideal.absNorm_mem _
  refine ⟨?_, hmem⟩
  have hne : normV v ≠ 0 := by
    rw [hc]; exact Ideal.absNorm_eq_zero_iff.not.2 v.ne_bot
  have h1 : normV v ≠ 1 := by
    rw [hc]
    intro h
    exact v.isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 h)
  omega

private theorem not_mem_of_coprime {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {p q : ℕ}
    (hq : (q : 𝓞 F) ∈ v.asIdeal) (h : Nat.Coprime q p) : (p : 𝓞 F) ∉ v.asIdeal := by
  intro hp
  apply v.isPrime.ne_top
  rw [Ideal.eq_top_iff_one]
  have hb := Nat.gcd_eq_gcd_ab q p
  rw [h] at hb
  have : ((1 : ℤ) : 𝓞 F) = (q : 𝓞 F) * ((q.gcdA p : ℤ) : 𝓞 F) + (p : 𝓞 F) * ((q.gcdB p : ℤ) : 𝓞 F) := by
    have := congrArg (Int.cast : ℤ → 𝓞 F) hb
    push_cast at this ⊢
    exact this
  rw [Int.cast_one] at this
  rw [this]
  exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ hq) (Ideal.mul_mem_right _ _ hp)

theorem UpperTheory.Gal.UnramifiedFromSplittingCriterion.unrCharPP :
    OrdPrime → CharOrd → DecPow → UnrCharPP := by
  intro hOrd hChar hDec ℓ k hℓ E Ω _ _ _ _ _ _ v
  haveI : IsAlgClosure (maximalRealSubfield E) Ω :=
    ⟨IsAlgClosure.isAlgClosed E, Algebra.IsAlgebraic.trans _ E Ω⟩
  obtain ⟨hq1, hqv⟩ := normV_mem v
  obtain ⟨p, hp, hBp, hdvd, hsplit⟩ := hOrd E Ω ℓ (k + 1) (normV v) (max (normV v) 2) hℓ hq1
  haveI : Fact p.Prime := ⟨hp⟩
  have hqp : normV v < p := lt_of_le_of_lt (le_max_left _ _) hBp
  have hcop : Nat.Coprime (normV v) p :=
    ((Nat.Prime.coprime_iff_not_dvd hp).2 (Nat.not_dvd_of_pos_of_lt (by omega) hqp)).symm
  have hpv : ((p : ℕ) : 𝓞 (maximalRealSubfield E)) ∉ v.asIdeal := not_mem_of_coprime v hqv hcop
  set a : (ZMod p)ˣ := ZMod.unitOfCoprime (normV v) hcop with ha
  have hao : ℓ ^ (k + 1) ∣ orderOf a := by
    rw [← orderOf_units]
    simpa [ha] using hdvd
  obtain ⟨lam, hlam1, hlamo⟩ := hChar p ℓ k a hℓ hao
  obtain ⟨ζ, hζ⟩ := exists_prim (F := maximalRealSubfield E) (Ω := Ω) p
  refine ⟨lam.comp (hζ.autToPow _), good_ker hζ lam hlam1, ?_, fun A hA => ⟨?_, fun φ hφ => ?_⟩⟩
  · intro t A hA
    by_cases hpt : ((p : ℕ) : 𝓞 (maximalRealSubfield E)) ∈ t.asIdeal
    · right
      intro g hg x
      have hval : A.valuation (p : Ω) < 1 := by
        have := (hA (p : 𝓞 (maximalRealSubfield E))).2 hpt
        simpa using this
      exact hsplit A hval g.toRingEquiv (fun z => apply_mem_iff_of_mem_Dec hg z) x
    · left
      intro τ hτ
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply,
        chi_one hζ τ ((hDec _ Ω A t hA p hp hpt ζ hζ).2 τ hτ), map_one]
  · intro τ hτ
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply,
      chi_one hζ τ ((hDec _ Ω A v hA p hp hpv ζ hζ).2 τ hτ), map_one]
  · have hN : ¬ A.valuation (p : Ω) < 1 := by
      simpa using not_valuation_lt_one_of_isPlaceOver hpv hA 1
    have hz1 : ζ ^ p = 1 := hζ.pow_eq_one
    have hv : A.valuation ζ ≤ 1 := by
      have h1 : A.valuation ζ ^ p = 1 := by rw [← map_pow, hz1, map_one]
      exact ((pow_eq_one_iff.1 h1).resolve_right hp.ne_zero).le
    have hφζ : φ ζ = ζ ^ normV v := by
      refine eq_of_pow_eq_one A hN ?_ ?_ (hφ.2 ζ hv)
      · rw [← map_pow, hz1, map_one]
      · rw [← pow_mul, mul_comm, pow_mul, hz1, one_pow]
    have h1 : hζ.autToPow (maximalRealSubfield E) φ = a := by
      apply Units.ext
      rw [chi_of_pow hζ φ _ hφζ, ha, ZMod.coe_unitOfCoprime]
    rw [MonoidHom.comp_apply, h1]
    exact hlamo
