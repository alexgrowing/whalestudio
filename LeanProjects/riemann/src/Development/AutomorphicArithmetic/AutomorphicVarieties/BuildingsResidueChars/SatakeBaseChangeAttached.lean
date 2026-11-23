import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SignAgreement.ExistsCompositumWithPrimeDegreeGalois
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.FrobeniusPowerCompatibility
import Development.AbelianVarietyTheory.BlockTheory.AdelicCMFields.UnitaryHeckeCharacterIdele

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published UpperTheory.V.Af.Sol

private theorem exists_not_mem_asIdeal_pow_of_ne_zero (K M : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] (w : HeightOneSpectrum (𝓞 M)) : ∃ f : ℕ, normV w = normV (HeightOneSpectrum.under (𝓞 K) w) ^ f := by
  refine ⟨(w.asIdeal.under (𝓞 K)).inertiaDeg' w.asIdeal, ?_⟩
  have h := Ideal.absNorm_eq_pow_inertiaDeg'_of_liesOver w.asIdeal (w.asIdeal.under (𝓞 K)) (Ideal.IsPrime.under _ _) (HeightOneSpectrum.under (𝓞 K) w).ne_bot
  simpa [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply] using h

private theorem tendsto_under_cofinite' (K M : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] : Filter.Tendsto (HeightOneSpectrum.under (𝓞 K) : HeightOneSpectrum (𝓞 M) → HeightOneSpectrum (𝓞 K)) Filter.cofinite Filter.cofinite := by
  refine Filter.Tendsto.cofinite_of_finite_preimage_singleton fun v => ?_
  have hfin := IsDedekindDomain.primesOver_finite v.asIdeal (𝓞 M)
  refine Set.Finite.to_subtype (Set.Finite.of_finite_image (f := HeightOneSpectrum.asIdeal) (hfin.subset ?_) (fun a _ b _ h => HeightOneSpectrum.ext h))
  rintro _ ⟨x, hx, rfl⟩
  simp only [Set.mem_preimage, Set.mem_singleton_iff] at hx
  subst hx
  exact ⟨x.isPrime, ⟨rfl⟩⟩

private theorem algSat_pow_map_pow (n q f : ℕ) (B : Multiset ℂˣ) : algSat n (q ^ f) (Multiset.map (fun x => x ^ f) B) = Multiset.map (fun x => x ^ f) (algSat n q B) := by
  unfold algSat
  simp only [Multiset.bind_map, Multiset.map_map, Function.comp_def, Multiset.bind_singleton, Multiset.pure_def, Multiset.bind_def]
  refine Multiset.map_congr rfl fun b _ => ?_
  rw [mul_pow]
  congr 1
  push_cast
  rw [← Complex.ofReal_pow, Real.rpow_pow_comm (by positivity)]

theorem UpperTheory.satake_base_change_attached :
    UpperTheory.V.Af.Sol.AttBc := by
  intro K M Ω _ _ _ _ _ _ _ _ _ _ _ l _ ι n r sat sat' huniq hbc hatt hss
  refine ⟨hss, ?_⟩
  have hT := UpperTheory.frobenius_power_compatibility K M Ω l ι
  filter_upwards [hbc, (tendsto_under_cofinite' K M).eventually hatt.2] with w hw hv
  obtain ⟨f, hf⟩ := exists_not_mem_asIdeal_pow_of_ne_zero K M w
  obtain ⟨B, hB, hE⟩ := hv
  obtain ⟨B0, hB0, hB0'⟩ := hw f hf
  obtain rfl := huniq _ _ _ hB hB0
  refine ⟨_, hB0', ?_⟩
  have h2 := (hT w f hf).1 n r _ hE
  rw [hf, algSat_pow_map_pow]
  exact h2
