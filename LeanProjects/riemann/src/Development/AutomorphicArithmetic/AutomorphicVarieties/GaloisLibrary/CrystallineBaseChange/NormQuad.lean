import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.BcStmt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChebotarevDegreeOne
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChebotarevDegreeOneIffCheb
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPadicAlgClRingEquivComplexCompEqOfCountabl
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterUnramifiedAeAndExistsLevel
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.FrobeniusPowerCompatibility
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsQuadraticSignCharacter
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.FrobeniusSignCompatibility
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenKerOfInfConn

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal
  GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published

private theorem normV_under {K K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] [Algebra K K']
    (w : HeightOneSpectrum (𝓞 K')) : normV w = normV (w.under (𝓞 K)) ^ w.asIdeal.inertiaDeg (𝓞 K) := by
  have : w.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal := ⟨rfl⟩
  have := w.isMaximal
  have := (w.under (𝓞 K)).isMaximal
  show Ideal.absNorm w.asIdeal = Ideal.absNorm (w.under (𝓞 K)).asIdeal ^ w.asIdeal.inertiaDeg (𝓞 K)
  rw [← Ideal.absNorm_relNorm (𝓞 K) (𝓞 K') w.asIdeal,
    Ideal.relNorm_eq_pow_of_isMaximal w.asIdeal (w.under (𝓞 K)).asIdeal, map_pow]

private theorem tendsto_under' {K K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] [Algebra K K'] :
    Filter.Tendsto (fun w : HeightOneSpectrum (𝓞 K') => w.under (𝓞 K)) Filter.cofinite Filter.cofinite := by
  refine Filter.Tendsto.cofinite_of_finite_preimage_singleton fun v => ?_
  have h0 : Ideal.map (algebraMap (𝓞 K) (𝓞 K')) v.asIdeal ≠ 0 :=
    fun h => v.ne_bot ((Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective _ _)).1 h)
  refine (Ideal.finite_factors h0).subset fun w hw => ?_
  have e : w.under (𝓞 K) = v := hw
  show w.asIdeal ∣ _
  rw [Ideal.dvd_iff_le, Ideal.map_le_iff_le_comap, ← e]
  exact le_rfl

theorem UpperTheory.V.Br.normQuad :
    UpperTheory.V.Br.NormQuad := by
  intro hG F E _ _ _ _ _ h2 η hN
  obtain ⟨hη1, hη, hN⟩ := hN
  rw [h2] at hη
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ι⟩ : Nonempty (Qbar 2 ≃+* ℂ) := GlobalTheory.nonempty_padicAlgCl_ringEquiv_complex 2
  let Ω := AlgebraicClosure E
  haveI : IsAlgClosure F Ω := ⟨IsAlgClosure.isAlgClosed E, Algebra.IsAlgebraic.trans F E Ω⟩
  obtain ⟨art, ha⟩ := hG F Ω
  obtain ⟨δ, hδc, hL⟩ := ha.exists_isLAdicOf ι (isAlgPos_zero_of_orderDvd (χ := η) two_pos hη)
  have hpow : δ ^ 2 = 1 := hL.pow_eq_one ha.quot.surjective hη
  have hE : ∀ v, η.UnrAt v → CharEig ι δ v (η.val v : ℂˣ) := fun v hv A hA =>
    ⟨(hL.unr_iff ha (Or.inr rfl) hA).2 hv, fun σ hσ => by
      rw [map_inv, Units.val_inv_eq_inv_val, hL.frob_unr ha (Or.inr rfl) hv hA hσ, inv_inv,
        RingEquiv.apply_symm_apply]⟩
  have hδ1 : δ ≠ 1 := by
    rintro rfl
    refine hη1 (Subtype.ext (MonoidHom.ext fun x => Units.ext ?_))
    obtain ⟨σ, hσ⟩ := toAb_surjective (art x)
    have e := hL x σ hσ.symm
    rw [infPow_zero, lPow_zero, inv_one, mul_one, mul_one, MonoidHom.one_apply, Units.val_one, eq_comm,
      map_eq_one_iff _ ι.symm.injective] at e
    exact e
  have hU : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, η.UnrAt (w.under (𝓞 F)) :=
    (tendsto_under' (K := F) (K' := E)).eventually (Filter.eventually_cofinite.2 (GlobalTheory.Mem.UnrAe.finite_ramified η))
  have hw : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, CharEig ι (δ.comp (res F Ω E)) w 1 := by
    filter_upwards [hN, hU] with w h1 h2
    have hf := normV_under (K := F) w
    have h3 := (UpperTheory.frobenius_power_compatibility F E Ω 2 ι w _ hf).2 δ _ (hE _ h2)
    rwa [← Units.val_pow_eq_pow_val, h1 _ hf, Units.val_one] at h3
  have key := GlobalTheory.Published.ChebotarevDegreeOne.eq_of_frob (F := E) (Ω := Ω) GlobalTheory.Published.chebotarevDegreeOne'
    (Filter.eventually_cofinite.1 hw) (f := fun s => δ (res F Ω E s)) (f' := fun _ => 1)
    (hδc.comp (continuous_restrictScalarsHom F E Ω)) continuous_const fun v hv _ A hA σ hσ => by
      have h := ((not_not.1 hv : CharEig _ _ _ _) A hA).2 σ hσ
      rw [map_eq_one_iff _ ι.injective, map_inv, Units.val_eq_one, inv_eq_one] at h
      exact h
  have hr : ∀ s ∈ (res F Ω E).range, δ s = 1 := by
    rintro _ ⟨s, rfl⟩
    exact congrFun key s
  obtain ⟨ε, -, -, hε, -⟩ := UpperTheory.exists_quadratic_sign_character F E Ω 2 h2
  have hs : IsSign E δ := by
    refine ⟨fun s => ⟨fun h => ?_, hr s⟩, fun s => ?_⟩
    · by_contra hn
      refine hδ1 (MonoidHom.ext fun t => ?_)
      by_cases ht : t ∈ (res F Ω E).range
      · exact hr t ht
      · have e1 := (hε.2 s).resolve_left fun h0 => hn ((hε.1 s).1 h0)
        have e2 := (hε.2 t).resolve_left fun h0 => ht ((hε.1 t).1 h0)
        have e3 := hr (s * t) ((hε.1 _).1 (by rw [map_mul, e1, e2]; simp))
        rwa [map_mul, h, one_mul] at e3
    · have e : δ s ^ 2 = 1 := DFunLike.congr_fun hpow s
      have e' : ((δ s : (Qbar 2)ˣ) : Qbar 2) ^ 2 = 1 := by rw [← Units.val_pow_eq_pow_val, e, Units.val_one]
      exact (sq_eq_one_iff.1 e').imp (fun h => Units.ext h) (fun h => Units.ext h)
  filter_upwards [hU] with w hu v hv
  obtain rfl : v = w.under (𝓞 F) := HeightOneSpectrum.ext hv
  refine ⟨hu, Units.ext ?_⟩
  obtain ⟨A, hA⟩ := exists_isPlaceOver Ω (w.under (𝓞 F))
  obtain ⟨φ, hφ⟩ := exists_isFrob hA
  have h1 := (hE _ hu A hA).2 φ hφ
  have h3 := (UpperTheory.frobenius_sign_compatibility F E Ω 2 ι δ hs w (fun A hA => (hE _ hu A hA).1) A hA).2 φ hφ
  refine (h1.symm.trans h3).trans ?_
  change _ = ((if normV w = normV (w.under (𝓞 F)) then 1 else -1 : ℂˣ) : ℂ)
  split_ifs <;> simp
