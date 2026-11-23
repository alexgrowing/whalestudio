import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.ThruBad
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.GammaLaurentFactors.LocalEmbeddingNorms.SuppFacts

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.CuspRep GroundTheory.Global.SemiLocal UpperTheory.V.Z.Gam

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

namespace UpperTheory.V.Z.Win.Birth

private theorem map_nm {K M : Type} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
    {v : HeightOneSpectrum (𝓞 K)} (w : PlacesOver M v) (hs : Function.Surjective (completionMap v w.1))
    (x : (w.1.adicCompletion M)ˣ) : Units.map (completionMap v w.1).toMonoidHom (nm w x) = x := by
  have hb : Function.Bijective (Algebra.linearMap (v.adicCompletion K) (w.1.adicCompletion M)) :=
    ⟨(completionMap v w.1).injective, hs⟩
  have h1 : Module.finrank (v.adicCompletion K) (w.1.adicCompletion M) = 1 := by
    rw [← (LinearEquiv.ofBijective _ hb).finrank_eq, Module.finrank_self]
  obtain ⟨y, hy⟩ := hs (x : w.1.adicCompletion M)
  refine Units.ext ?_
  change completionMap v w.1 (Algebra.norm (v.adicCompletion K) (x : w.1.adicCompletion M)) = x
  rw [← hy]
  have h2 : Algebra.norm (v.adicCompletion K) (completionMap v w.1 y) = y ^ Module.finrank (v.adicCompletion K) (w.1.adicCompletion M) :=
    Algebra.norm_algebraMap y
  rw [h2, h1, pow_one]

private theorem thru_split {K M : Type} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
    {v : HeightOneSpectrum (𝓞 K)} (w : PlacesOver M v) (hs : Function.Surjective (completionMap v w.1))
    (ζ : (w.1.adicCompletion M)ˣ →* ℂˣ) (hζ : IsSmoothChar ζ) :
    ∃ χ : (v.adicCompletion K)ˣ →* ℂˣ, IsSmoothChar χ ∧ IsUnram (ζ * χ.comp (nm w)) := by
  have hc : Continuous (Units.map (completionMap v w.1).toMonoidHom) :=
    Continuous.units_map _ (continuous_completionMap v w.1)
  refine ⟨(ζ.comp (Units.map (completionMap v w.1).toMonoidHom))⁻¹, ?_, fun x _ => ?_⟩
  · have he : (((ζ.comp (Units.map (completionMap v w.1).toMonoidHom))⁻¹).ker : Set (v.adicCompletion K)ˣ) =
        Units.map (completionMap v w.1).toMonoidHom ⁻¹' (ζ.ker : Set _) := by
      ext y
      simp [MonoidHom.mem_ker]
    change IsOpen _
    rw [he]
    exact hζ.preimage hc
  · change ζ x * (ζ (Units.map (completionMap v w.1).toMonoidHom (nm w x)))⁻¹ = 1
    rw [map_nm w hs x, mul_inv_cancel]

end UpperTheory.V.Z.Win.Birth

open UpperTheory.V.Z.Win.Birth in
theorem UpperTheory.V.Z.Win.Birth.thruBad :
    UpperTheory.V.Z.Win.Birth.ThruBad := by
  intro K M _ _ _ _ _ _ _ _ π hbad v w s hs ζ hζ hmem
  by_cases hsp : UpperTheory.ConvolutionTheory.GM.Split M v
  · exact thru_split w (hsp w) ζ hζ
  · have hw : w.1.under (𝓞 K) = v := HeightOneSpectrum.ext w.2.over.symm
    obtain ⟨B, hB⟩ := (hbad v hsp).2 w.1 hw
    obtain ⟨μ, hμ, e⟩ := (suppFacts M 2 (by norm_num) π w.1).2.2.2.1 s B hs hB _ hmem
    obtain rfl : ζ = μ := IrrGL.ofChar_inj.1 e
    exact ⟨1, isSmoothChar_one, by simpa using hμ⟩
