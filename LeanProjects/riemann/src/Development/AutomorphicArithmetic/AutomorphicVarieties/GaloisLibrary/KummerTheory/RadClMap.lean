import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Mk0IdMapCongr
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ClMapBasic

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

private theorem intValuation_mapRingEquiv {K K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K']
    (τ : K ≃+* K') (v : HeightOneSpectrum (𝓞 K)) (x : 𝓞 K) :
    (HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv τ) v).intValuation
      (RingOfIntegers.mapRingEquiv τ x) = v.intValuation x := by
  set ρ := RingOfIntegers.mapRingEquiv τ
  have hw : (HeightOneSpectrum.equivOfRingEquiv ρ v).asIdeal = Ideal.map ρ v.asIdeal := by
    ext y
    rw [Ideal.mem_map_of_equiv]
    show ρ.symm y ∈ v.asIdeal ↔ _
    constructor
    · intro h
      exact ⟨_, h, ρ.apply_symm_apply y⟩
    · rintro ⟨z, hz, rfl⟩
      rwa [ρ.symm_apply_apply]
  by_cases hx : x = 0
  · subst hx
    simp
  have hx' : ρ x ≠ 0 := (map_ne_zero_iff ρ ρ.injective).mpr hx
  rw [HeightOneSpectrum.intValuation_eq_exp_neg_multiplicity _ hx,
    HeightOneSpectrum.intValuation_eq_exp_neg_multiplicity _ hx']
  have hm : multiplicity (HeightOneSpectrum.equivOfRingEquiv ρ v).asIdeal (Ideal.span {ρ x}) =
      multiplicity v.asIdeal (Ideal.span {x}) := by
    apply multiplicity_eq_of_emultiplicity_eq
    rw [emultiplicity_eq_emultiplicity_iff]
    intro k
    have hs : Ideal.span {ρ x} = Ideal.map ρ (Ideal.span {x}) := by
      rw [Ideal.map_span, Set.image_singleton]
    rw [Ideal.dvd_iff_le, Ideal.dvd_iff_le, hw, hs, ← Ideal.map_pow]
    constructor
    · intro h
      have h2 := Ideal.comap_mono (f := ρ) h
      rwa [Ideal.comap_map_of_bijective _ ρ.bijective, Ideal.comap_map_of_bijective _ ρ.bijective] at h2
    · exact Ideal.map_mono
  rw [hm]

private theorem ordv_units_map_ringEquiv {K K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K']
    (τ : K ≃+* K') (v : HeightOneSpectrum (𝓞 K)) (a : Kˣ) :
    ordv (HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv τ) v)
      (Units.map τ.toMonoidHom a) = ordv v a := by
  have hτ : ∀ z : 𝓞 K, τ (algebraMap (𝓞 K) K z) =
      algebraMap (𝓞 K') K' (RingOfIntegers.mapRingEquiv τ z) := fun z =>
    (RingOfIntegers.mapRingEquiv_apply τ z).symm
  have hval : (HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv τ) v).valuationOfNeZero
      (Units.map τ.toMonoidHom a) = v.valuationOfNeZero a := by
    rw [← WithZero.coe_inj, HeightOneSpectrum.valuationOfNeZero_eq,
      HeightOneSpectrum.valuationOfNeZero_eq]
    obtain ⟨x, y, -, hxy⟩ := IsFractionRing.div_surjective (𝓞 K) (a : K)
    show HeightOneSpectrum.valuation K' _ (τ (a : K)) = HeightOneSpectrum.valuation K v (a : K)
    rw [← hxy, map_div₀, map_div₀, map_div₀, hτ, hτ, HeightOneSpectrum.valuation_of_algebraMap,
      HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap,
      HeightOneSpectrum.valuation_of_algebraMap, intValuation_mapRingEquiv, intValuation_mapRingEquiv]
  unfold ordv
  rw [hval]

theorem UpperTheory.V.Kum.radClMap :
    ∀ (K K' : Type) [Field K] [NumberField K] [Field K'] [NumberField K'] (τ : K ≃+* K') (n : ℕ) (a : Kˣ), clMap τ (radCl n a) = radCl n (Units.map τ.toMonoidHom a) := by
  intro K K' _ _ _ _ τ n a
  have hinv : ∀ w : 𝓞 K, RingOfIntegers.mapRingEquiv τ.symm (RingOfIntegers.mapRingEquiv τ w) = w :=
    fun w => RingOfIntegers.ext (by simp [RingOfIntegers.mapRingEquiv_apply])
  have hback : ∀ I, clMap τ.symm (clMap τ (ClassGroup.mk0 I)) = ClassGroup.mk0 I := by
    intro I
    rw [class_map_mk0, class_map_mk0]
    congr 1
    apply Subtype.ext
    show Ideal.map (RingOfIntegers.mapRingEquiv τ.symm)
      (Ideal.map (RingOfIntegers.mapRingEquiv τ) (I : Ideal (𝓞 K))) = I
    ext y
    rw [Ideal.mem_map_of_equiv]
    constructor
    · rintro ⟨z, hz, rfl⟩
      rw [Ideal.mem_map_of_equiv] at hz
      obtain ⟨w, hw, rfl⟩ := hz
      rwa [hinv]
    · intro hy
      exact ⟨RingOfIntegers.mapRingEquiv τ y, (Ideal.mem_map_of_equiv _ _).mpr ⟨y, hy, rfl⟩, hinv y⟩
  have hinj : Function.Injective (clMap τ) := by
    intro x y hxy
    obtain ⟨I, rfl⟩ := ClassGroup.mk0_surjective x
    obtain ⟨J, rfl⟩ := ClassGroup.mk0_surjective y
    rw [← hback I, ← hback J, hxy]
  unfold radCl
  rw [MonoidHom.map_finprod_of_injective _ hinj,
    ← finprod_comp_equiv (HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv τ))]
  refine finprod_congr (fun v => ?_)
  rw [map_zpow, ordv_units_map_ringEquiv]
  congr 1
  show clMap τ (ClassGroup.mk0 _) = ClassGroup.mk0 _
  rw [class_map_mk0]
  congr 1
  apply Subtype.ext
  show Ideal.map (RingOfIntegers.mapRingEquiv τ) v.asIdeal = _
  ext y
  rw [Ideal.mem_map_of_equiv]
  show _ ↔ (RingOfIntegers.mapRingEquiv τ).symm y ∈ v.asIdeal
  constructor
  · rintro ⟨z, hz, rfl⟩
    rwa [RingEquiv.symm_apply_apply]
  · intro h
    exact ⟨_, h, RingEquiv.apply_symm_apply _ y⟩
