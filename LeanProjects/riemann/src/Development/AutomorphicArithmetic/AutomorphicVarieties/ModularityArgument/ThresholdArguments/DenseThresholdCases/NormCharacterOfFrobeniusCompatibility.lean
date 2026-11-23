import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.NormCharacterOfFrobeniusCompatibility
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutomorphicFormHyp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LitAut

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published UpperTheory.V.Af.Sol
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
theorem UpperTheory.norm_character_of_printed_char_frobenius :
    _root_.UpperTheory.V.Af.Hypotheses' → UpperTheory.V.Af.Sol.CharFrob → UpperTheory.V.Af.Sol.NormChar := by
  intro P hC K M Ω _ _ _ _ _ _ _ _ _ _ _ l _ ι η hη
  rcases hη with rfl | hN
  · exact ⟨1, rfl, Filter.Eventually.of_forall fun v => charEig_one ι v⟩
  obtain ⟨art, ha⟩ := P.litN.aut.art K Ω
  have hm : 0 < Module.finrank K M := Module.finrank_pos
  have hA : IsAlgPos η 0 := isAlgPos_zero_of_orderDvd (χ := η) hm hN.2.1
  obtain ⟨δ, hδc, hL⟩ := ha.exists_isLAdicOf ι hA
  have hE := hC K Ω l ι η δ ⟨hδc, art, 0, ha, hA, hL⟩
  refine ⟨δ, ?_, hE.mono fun v hv => hv.2⟩
  have hw : ∀ᶠ w : HeightOneSpectrum (𝓞 M) in Filter.cofinite, CharEig ι (δ.comp (res K Ω M)) w 1 := by
    filter_upwards [hN.2.2, (tendsto_under' (K := K) (K' := M)).eventually hE] with w h1 h2
    have hf := normV_under (K := K) w
    have h3 := (UpperTheory.frobenius_power_compatibility K M Ω l ι w _ hf).2 δ _ h2.2
    rwa [← Units.val_pow_eq_pow_val, h1 _ hf, Units.val_one] at h3
  have key := GlobalTheory.Published.ChebotarevDegreeOne.eq_of_frob (F := M) (Ω := Ω) GlobalTheory.Published.chebotarevDegreeOne'
    (Filter.eventually_cofinite.1 hw) (f := fun s => δ (res K Ω M s)) (f' := fun _ => 1)
    (hδc.comp (continuous_restrictScalarsHom K M Ω)) continuous_const fun v hv _ A hA σ hσ => by
      have h := ((not_not.1 hv : CharEig _ _ _ _) A hA).2 σ hσ
      rw [map_eq_one_iff _ ι.injective, map_inv, Units.val_eq_one, inv_eq_one] at h
      exact h
  exact MonoidHom.ext fun s => congrFun key s
end
