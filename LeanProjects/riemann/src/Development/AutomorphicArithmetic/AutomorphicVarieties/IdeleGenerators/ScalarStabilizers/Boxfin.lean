import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.WeightChange
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd

private theorem abs_reAt {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (v : InfinitePlace F) (x : F) :
    |reAt v x| = v x := by
  have hr := IsTotallyReal.isReal v
  rw [← InfinitePlace.norm_embedding_eq, ← InfinitePlace.embedding_of_isReal_apply hr, Complex.norm_real, reAt,
    ← InfinitePlace.embedding_of_isReal_apply hr, Complex.ofReal_re, Real.norm_eq_abs]

private theorem val_le {F : Type} [Field F] [NumberField F] (w : HeightOneSpectrum (𝓞 F)) {I : Ideal (𝓞 F)} (hI : I ≠ ⊥)
    {d : 𝓞 F} (hd : d ∈ I) : w.valuation F (d : F) ≤ WithZero.exp (-(ordI w I : ℤ)) := by
  have h1 : w.asIdeal ^ ordI w I ∣ I := by
    rw [← Associates.mk_dvd_mk, Associates.mk_pow]
    exact (Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero.2 hI) w.associates_irreducible).2 le_rfl
  have h2 : d ∈ w.asIdeal ^ ordI w I := Ideal.le_of_dvd h1 hd
  rw [show (d : F) = algebraMap (𝓞 F) F d from rfl, HeightOneSpectrum.valuation_of_algebraMap]
  exact (HeightOneSpectrum.intValuation_le_pow_iff_mem w d _).2 h2

private theorem val_pLoc {F : Type} [Field F] [NumberField F] (w : HeightOneSpectrum (𝓞 F)) (x : F) :
    Valued.v (pLoc F w (algebraMap F (Af F) x)) = w.valuation F x :=
  HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w x

theorem UpperTheory.V.Sd.Hm.boxfin :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (y : (Af F)ˣ) (ξ : F),
        {η : F | (∀ v, 0 < reAt v η) ∧ (∀ v, reAt v η < reAt v ξ) ∧ ∃ 𝔪, GenD (algebraMap F (Af F) η * (y : Af F)) 𝔪}.Finite := by
  intro F _ _ _ y ξ
  by_cases hne : ∃ η₀ : F, ∃ 𝔪, GenD (algebraMap F (Af F) η₀ * (y : Af F)) 𝔪
  swap
  · convert Set.finite_empty
    ext η
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    exact fun h => hne ⟨η, h.2.2⟩
  obtain ⟨η₀, 𝔪₀, h₀⟩ := hne
  obtain ⟨d, hd, hd0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h₀.1
  obtain ⟨w₀⟩ : Nonempty (HeightOneSpectrum (𝓞 F)) := by
    obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 F)
    exact ⟨⟨M, hM.isPrime, RingOfIntegers.not_isField F |> Ring.ne_bot_of_isMaximal_of_not_isField hM⟩⟩
  have hη₀ : η₀ ≠ 0 := by
    rintro rfl
    have := h₀.2 w₀
    rw [map_zero, zero_mul, map_zero, map_zero] at this
    exact WithZero.exp_ne_zero this.symm
  have hc : (d : F) / η₀ ≠ 0 := div_ne_zero (by exact_mod_cast hd0) hη₀
  refine Set.Finite.of_finite_image (f := fun η => (d : F) / η₀ * η) ?_ (mul_right_injective₀ hc).injOn
  refine (Embeddings.finite_of_norm_le F ℂ (∑ v : InfinitePlace F, v ((d : F) / η₀ * ξ))).subset ?_
  rintro _ ⟨η, ⟨hpos, hlt, 𝔪, h⟩, rfl⟩
  refine ⟨?_, fun φ => ?_⟩
  · obtain ⟨r, hr⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 F) F ((d : F) / η₀ * η) fun w => by
      have a := h.2 w
      have a₀ := h₀.2 w
      rw [map_mul, map_mul, val_pLoc] at a a₀
      have hy : Valued.v (pLoc F w (y : Af F)) ≠ 0 := (right_ne_zero_of_mul (a ▸ WithZero.exp_ne_zero))
      rw [← eq_div_iff hy] at a a₀
      have e : w.valuation F η / w.valuation F η₀ = WithZero.exp ((ordI w 𝔪₀ : ℤ) - (ordI w 𝔪 : ℤ)) := by
        rw [a, a₀, div_div_div_cancel_right₀ hy, ← WithZero.exp_sub]
        congr 1; ring
      rw [div_mul_eq_mul_div, mul_div_assoc, map_mul, map_div₀, e]
      calc _ ≤ WithZero.exp (-(ordI w 𝔪₀ : ℤ)) * WithZero.exp ((ordI w 𝔪₀ : ℤ) - (ordI w 𝔪 : ℤ)) :=
            mul_le_mul_left (val_le w h₀.1 hd) _
        _ ≤ 1 := by
            rw [← WithZero.exp_add, ← WithZero.exp_zero, WithZero.exp_le_exp]
            omega
    show IsIntegral ℤ ((d : F) / η₀ * η)
    rw [← hr]
    exact r.2
  · show ‖φ ((d : F) / η₀ * η)‖ ≤ _
    rw [← InfinitePlace.apply]
    refine le_trans ?_ (Finset.single_le_sum (f := fun v : InfinitePlace F => v ((d : F) / η₀ * ξ))
      (fun v _ => apply_nonneg v _) (Finset.mem_univ (InfinitePlace.mk φ)))
    simp only [map_mul]
    refine mul_le_mul_of_nonneg_left ?_ (apply_nonneg _ _)
    rw [← abs_reAt, ← abs_reAt, abs_of_pos (hpos _)]
    exact (hlt _).le.trans (le_abs_self _)
