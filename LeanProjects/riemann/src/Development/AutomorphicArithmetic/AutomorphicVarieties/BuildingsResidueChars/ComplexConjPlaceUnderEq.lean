import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SignAgreement.ExistsCompositumWithPrimeDegreeGalois
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BcPolar
import Development.AutomorphicArithmetic.AutomorphicVarieties.PartsConj
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published UpperTheory.V.Af.Sol

private theorem cPl_asIdeal {E : Type} [Field E] [NumberField E] [IsCMField E] (w : HeightOneSpectrum (𝓞 E)) :
    (cPl w).asIdeal = w.asIdeal.comap (RingOfIntegers.mapRingEquiv (IsCMField.complexConj E).toRingEquiv : 𝓞 E →+* 𝓞 E) :=
  (GlobalTheory.Mem.Chr.conjPl_iff_comap _ _ _).1 (conjPl_conjSrc _ w)

private theorem conj_algebraMap {K M : Type} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
    [IsCMField K] [IsCMField M] (x : K) :
    IsCMField.complexConj M (algebraMap K M x) = algebraMap K M (IsCMField.complexConj K x) := by
  obtain ⟨j⟩ : Nonempty (M →+* ℂ) := inferInstance
  apply j.injective
  rw [IsCMField.complexEmbedding_complexConj M j]
  exact (IsCMField.complexEmbedding_complexConj K (j.comp (algebraMap K M)) x).symm

theorem UpperTheory.complexConj_place_under_eq :
    UpperTheory.V.Af.Sol.ConjUnder := by
  intro K M _ _ _ _ _ _ _ w
  refine ⟨?_, ?_, ?_⟩
  · apply HeightOneSpectrum.ext
    rw [cPl_asIdeal]
    change (cPl w).asIdeal.comap (algebraMap (𝓞 K) (𝓞 M)) = (w.asIdeal.comap (algebraMap (𝓞 K) (𝓞 M))).comap _
    rw [cPl_asIdeal, Ideal.comap_comap, Ideal.comap_comap]
    congr 1
    ext x
    exact conj_algebraMap (x : K)
  · show Nat.card (𝓞 M ⧸ (cPl w).asIdeal) = Nat.card (𝓞 M ⧸ w.asIdeal)
    refine Nat.card_congr (Ideal.quotientEquiv _ _
      (RingOfIntegers.mapRingEquiv (IsCMField.complexConj M).toRingEquiv) ?_).toEquiv
    rw [cPl_asIdeal]
    exact (Ideal.map_comap_of_surjective
      (RingOfIntegers.mapRingEquiv (IsCMField.complexConj M).toRingEquiv : 𝓞 M →+* 𝓞 M)
      (RingOfIntegers.mapRingEquiv _).surjective w.asIdeal).symm
  · apply HeightOneSpectrum.ext
    rw [cPl_asIdeal, cPl_asIdeal, Ideal.comap_comap]
    convert Ideal.comap_id w.asIdeal
    ext x
    exact IsCMField.complexConj_apply_apply M (x : M)
