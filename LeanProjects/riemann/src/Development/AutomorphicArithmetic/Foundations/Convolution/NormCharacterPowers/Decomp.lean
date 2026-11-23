import Development.AutomorphicArithmetic.Foundations.Convolution.NormCharacterPowers.SumSatUnit
import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.JacquetShalikaRigidity
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlobalArtinReciprocityHolds
import Development.AbelianVarietyTheory.BlockTheory.AdelicCMFields.UnitaryHeckeCharacterIdele

open UpperTheory.ConvolutionTheory.R
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual

section

variable (K M : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]

private theorem normV_inertia (w : HeightOneSpectrum (𝓞 M)) :
    normV w = normV (w.under (𝓞 K)) ^ w.asIdeal.inertiaDeg (𝓞 K) := by
  have : w.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal := ⟨rfl⟩
  have := w.isMaximal
  have := (w.under (𝓞 K)).isMaximal
  show Ideal.absNorm w.asIdeal = Ideal.absNorm (w.under (𝓞 K)).asIdeal ^ w.asIdeal.inertiaDeg (𝓞 K)
  rw [← Ideal.absNorm_relNorm (𝓞 K) (𝓞 M) w.asIdeal,
    Ideal.relNorm_eq_pow_of_isMaximal w.asIdeal (w.under (𝓞 K)).asIdeal, map_pow]

private theorem unram_ae : ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
    ∀ w : HeightOneSpectrum (𝓞 M), w.under (𝓞 K) = v → w.asIdeal.ramificationIdx (𝓞 K) = 1 := by
  have hfin : {w : HeightOneSpectrum (𝓞 M) | w.asIdeal ∣ differentIdeal (𝓞 K) (𝓞 M)}.Finite :=
    Ideal.finite_factors differentIdeal_ne_bot
  refine Filter.eventually_cofinite.2 ((hfin.image fun w => w.under (𝓞 K)).subset ?_)
  intro v hv
  by_contra hn
  refine hv fun w hw => ?_
  have := w.isPrime
  have hnd : ¬ w.asIdeal ∣ differentIdeal (𝓞 K) (𝓞 M) := fun h => hn ⟨w, h, hw⟩
  exact Ideal.ramificationIdx_eq_one_iff.2 (not_dvd_differentIdeal_iff.1 hnd)

private theorem card_fibre (v : HeightOneSpectrum (𝓞 K)) :
    Nat.card {w : HeightOneSpectrum (𝓞 M) // w.under (𝓞 K) = v} = (v.asIdeal.primesOver (𝓞 M)).ncard := by
  rw [← Nat.card_coe_set_eq]
  refine Nat.card_congr (Equiv.ofBijective
    (fun w => ⟨w.1.asIdeal, w.1.isPrime, ⟨(congrArg HeightOneSpectrum.asIdeal w.2).symm⟩⟩) ⟨fun a b h => ?_, fun P => ?_⟩)
  · exact Subtype.ext (HeightOneSpectrum.ext (congrArg Subtype.val h))
  · obtain ⟨P, hP, hPv⟩ := P
    exact ⟨⟨⟨P, hP, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot P⟩,
      HeightOneSpectrum.ext hPv.over.symm⟩, rfl⟩

end

theorem UpperTheory.ConvolutionTheory.R.decomp :
    Decomp := by
  intro K M _ _ _ _ _ _ _ _ hl
  filter_upwards [unram_ae K M] with v hv
  have := v.isPrime
  have hfund := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn v.asIdeal (𝓞 M) Gal(M/K)
  obtain ⟨⟨P, hP, hPv⟩⟩ := (inferInstance : Nonempty (v.asIdeal.primesOver (𝓞 M)))
  have he : v.asIdeal.ramificationIdxIn (𝓞 M) = 1 := by
    rw [Ideal.ramificationIdxIn_eq_ramificationIdx v.asIdeal P Gal(M/K)]
    exact hv ⟨P, hP, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot P⟩ (HeightOneSpectrum.ext hPv.over.symm)
  have hn : ∀ w : HeightOneSpectrum (𝓞 M), w.under (𝓞 K) = v →
      normV w = normV v ^ v.asIdeal.inertiaDegIn (𝓞 M) := by
    rintro w rfl
    have := w.isPrime
    have : w.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal := ⟨rfl⟩
    rw [Ideal.inertiaDegIn_eq_inertiaDeg _ w.asIdeal Gal(M/K)]
    exact normV_inertia K M w
  rw [he, one_mul, IsGalois.card_aut_eq_finrank, ← card_fibre] at hfund
  rcases hl.eq_one_or_self_of_dvd _ (Dvd.intro_left _ hfund) with h | h
  · rw [h, mul_one] at hfund
    exact Or.inl ⟨hfund, fun w hw => by rw [hn w hw, h, pow_one]⟩
  · rw [h] at hfund
    exact Or.inr ⟨Nat.eq_of_mul_eq_mul_right hl.pos (hfund.trans (one_mul _).symm),
      fun w hw => by rw [hn w hw, h]⟩
