import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LatticeBlockClasses.CBlockValAlt

open NumberField IsDedekindDomain UpperTheory.V UpperTheory.V.KL UpperTheory.V.ZK UpperTheory.V.ZK.Cl

private theorem mem_eqv {R : Type} [CommRing R] (e : R ≃+* R) (P : HeightOneSpectrum R) (y : R) :
    y ∈ (HeightOneSpectrum.equivOfRingEquiv e P).asIdeal ↔ e.symm y ∈ P.asIdeal := Iff.rfl

private theorem mem_pow_eqv {R : Type} [CommRing R] (e : R ≃+* R) (P : HeightOneSpectrum R) (y : R) (n : ℕ) :
    e y ∈ (HeightOneSpectrum.equivOfRingEquiv e P).asIdeal ^ n ↔ y ∈ P.asIdeal ^ n := by
  have h : (HeightOneSpectrum.equivOfRingEquiv e P).asIdeal = Ideal.map (e : R →+* R) P.asIdeal := by
    rw [Ideal.map_comap_of_equiv]
    rfl
  rw [h, ← Ideal.map_pow, Ideal.map_comap_of_equiv, Ideal.mem_comap]
  simp

private theorem intVal_eqv {R : Type} [CommRing R] [IsDedekindDomain R] (e : R ≃+* R) (P : HeightOneSpectrum R) (y : R) :
    (HeightOneSpectrum.equivOfRingEquiv e P).intValuation (e y) = P.intValuation y := by
  set Q := HeightOneSpectrum.equivOfRingEquiv e P
  have key : ∀ n : ℕ, Q.intValuation (e y) ≤ WithZero.exp (-(n : ℤ)) ↔
      P.intValuation y ≤ WithZero.exp (-(n : ℤ)) := by
    intro n
    rw [HeightOneSpectrum.intValuation_le_pow_iff_dvd, HeightOneSpectrum.intValuation_le_pow_iff_dvd,
      Ideal.dvd_iff_le, Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem,
      Ideal.span_singleton_le_iff_mem]
    exact mem_pow_eqv e P y n
  by_cases hy : y = 0
  · simp [hy]
  have hey : e y ≠ 0 := by simpa using hy
  have form : ∀ (v : HeightOneSpectrum R) (r : R), r ≠ 0 →
      ∃ m : ℕ, v.intValuation r = WithZero.exp (-(m : ℤ)) :=
    fun v r hr => ⟨_, by rw [HeightOneSpectrum.intValuation_def, if_neg hr]⟩
  obtain ⟨m1, h1⟩ := form Q _ hey
  obtain ⟨m2, h2⟩ := form P _ hy
  rw [h1, h2] at key ⊢
  have a := (key m1).1 le_rfl
  have b := (key m2).2 le_rfl
  rw [WithZero.exp_le_exp] at a b
  have : m1 = m2 := by omega
  rw [this]

theorem UpperTheory.V.ZK.Cl.cAct :
    UpperTheory.V.ZK.Cl.CAct := by
  intro L F _ _ _ _ _
  have val : ∀ (σ : Gal(F/L)) (P : HeightOneSpectrum (𝓞 F)) (x : F),
      HeightOneSpectrum.valuation F (actP σ P) (σ x) = HeightOneSpectrum.valuation F P x := by
    intro σ P x
    obtain ⟨p, q, -, hpq⟩ := IsFractionRing.div_surjective (𝓞 F) x
    have hpq' : (p : F) / q = x := hpq
    have hσ : ∀ a : 𝓞 F, σ (a : F) = ((RingOfIntegers.mapRingEquiv σ.toRingEquiv a : 𝓞 F) : F) :=
      fun a => by rw [RingOfIntegers.mapRingEquiv_apply]; rfl
    rw [← hpq', map_div₀, hσ, hσ, map_div₀, map_div₀, HeightOneSpectrum.valuation_of_algebraMap,
      HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap,
      HeightOneSpectrum.valuation_of_algebraMap]
    unfold actP
    rw [intVal_eqv, intVal_eqv]
  have sym : ∀ (σ : Gal(F/L)) (y : 𝓞 F),
      (((RingOfIntegers.mapRingEquiv σ.toRingEquiv).symm y : 𝓞 F) : F) = σ.symm (y : F) := by
    intro σ y
    apply σ.injective
    rw [AlgEquiv.apply_symm_apply]
    have := RingOfIntegers.mapRingEquiv_apply σ.toRingEquiv
      ((RingOfIntegers.mapRingEquiv σ.toRingEquiv).symm y)
    rw [RingEquiv.apply_symm_apply] at this
    exact this.symm
  have memA : ∀ (σ : Gal(F/L)) (P : HeightOneSpectrum (𝓞 F)) (y : 𝓞 F),
      y ∈ (actP σ P).asIdeal ↔ (RingOfIntegers.mapRingEquiv σ.toRingEquiv).symm y ∈ P.asIdeal :=
    fun σ P y => mem_eqv _ P y
  refine ⟨val, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro σ τ P
    apply HeightOneSpectrum.ext
    ext y
    rw [memA, memA, memA]
    have h : (((RingOfIntegers.mapRingEquiv (σ * τ).toRingEquiv).symm y : 𝓞 F) : F) =
        (((RingOfIntegers.mapRingEquiv τ.toRingEquiv).symm
          ((RingOfIntegers.mapRingEquiv σ.toRingEquiv).symm y) : 𝓞 F) : F) := by
      rw [sym, sym, sym]
      rfl
    rw [show (RingOfIntegers.mapRingEquiv (σ * τ).toRingEquiv).symm y =
        (RingOfIntegers.mapRingEquiv τ.toRingEquiv).symm
          ((RingOfIntegers.mapRingEquiv σ.toRingEquiv).symm y) from by exact_mod_cast h]
  · intro P
    apply HeightOneSpectrum.ext
    ext y
    rw [memA]
    have h : (((RingOfIntegers.mapRingEquiv (1 : Gal(F/L)).toRingEquiv).symm y : 𝓞 F) : F) =
        (y : F) := by
      rw [sym]
      rfl
    rw [show (RingOfIntegers.mapRingEquiv (1 : Gal(F/L)).toRingEquiv).symm y = y from by
      exact_mod_cast h]
  · intro σ P b
    rw [memA]
    have h1 : algebraMap (𝓞 L) F b = ((algebraMap (𝓞 L) (𝓞 F) b : 𝓞 F) : F) := by
      rw [IsScalarTower.algebraMap_apply (𝓞 L) (𝓞 F) F]
    have h2 : algebraMap (𝓞 L) F b = algebraMap L F (b : L) := by
      rw [IsScalarTower.algebraMap_apply (𝓞 L) L F]
    have hc : ((algebraMap (𝓞 L) (𝓞 F) b : 𝓞 F) : F) = algebraMap L F (b : L) := by
      rw [← h1, h2]
    have h : (((RingOfIntegers.mapRingEquiv σ.toRingEquiv).symm (algebraMap (𝓞 L) (𝓞 F) b) : 𝓞 F) : F)
        = ((algebraMap (𝓞 L) (𝓞 F) b : 𝓞 F) : F) := by
      rw [sym, hc, AlgEquiv.commutes]
    rw [show (RingOfIntegers.mapRingEquiv σ.toRingEquiv).symm (algebraMap (𝓞 L) (𝓞 F) b) =
        algebraMap (𝓞 L) (𝓞 F) b from by exact_mod_cast h]
  · intro σ P α
    unfold ordP
    have : ((actU σ α : Fˣ) : F) = σ (α : F) := rfl
    rw [this, val]
  · intro P α β
    unfold ordP
    rw [Units.val_mul, map_mul, WithZero.log_mul (by simp) (by simp)]
    ring
  · intro P α n
    unfold ordP
    rw [Units.val_zpow_eq_zpow_val, map_zpow₀, WithZero.log_zpow, smul_eq_mul]
    ring
