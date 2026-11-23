import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BcDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AdTransfer
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RTwist
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published

private theorem normV_under {K K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] [Algebra K K']
    (w : HeightOneSpectrum (𝓞 K')) : normV w = normV (w.under (𝓞 K)) ^ w.asIdeal.inertiaDeg (𝓞 K) := by
  have : w.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal := ⟨rfl⟩
  have := w.isMaximal
  have := (w.under (𝓞 K)).isMaximal
  show Ideal.absNorm w.asIdeal = Ideal.absNorm (w.under (𝓞 K)).asIdeal ^ w.asIdeal.inertiaDeg (𝓞 K)
  rw [← Ideal.absNorm_relNorm (𝓞 K) (𝓞 K') w.asIdeal,
    Ideal.relNorm_eq_pow_of_isMaximal w.asIdeal (w.under (𝓞 K)).asIdeal, map_pow]

private theorem cPl_asIdeal {E : Type} [Field E] [NumberField E] [IsCMField E] (w : HeightOneSpectrum (𝓞 E)) :
    (cPl w).asIdeal = w.asIdeal.comap (RingOfIntegers.mapRingEquiv (IsCMField.complexConj E).toRingEquiv) :=
  (GlobalTheory.Mem.Chr.conjPl_iff_comap _ _ _).1 (conjPl_conjSrc _ w)

private theorem normV_cPl {E : Type} [Field E] [NumberField E] [IsCMField E] (w : HeightOneSpectrum (𝓞 E)) :
    normV (cPl w) = normV w := by
  show Ideal.absNorm (cPl w).asIdeal = Ideal.absNorm w.asIdeal
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  refine (Nat.card_congr (Ideal.quotientEquiv _ _
    (RingOfIntegers.mapRingEquiv (IsCMField.complexConj E).toRingEquiv).symm ?_).toEquiv).symm
  rw [cPl_asIdeal]
  exact (Ideal.map_symm _).symm

private theorem conj_algebraMap {F E : Type} [Field F] [NumberField F] [IsTotallyReal F] [Field E] [NumberField E] [IsCMField E]
    [Algebra F E] (x : F) : IsCMField.complexConj E (algebraMap F E x) = algebraMap F E x := by
  rw [IsCMField.complexConj_eq_self_iff, mem_maximalRealSubfield_iff]
  intro φ
  have h := IsTotallyReal.complexEmbedding_isReal (φ.comp (algebraMap F E))
  exact RingHom.congr_fun h x

theorem UpperTheory.baseChange_complexConj_invariance :
    UpperTheory.V.Af.Bc.BcConj := by
  intro F E _ _ _ _ _ _ _ n π P h
  have h1 := h.unr
  have h2 := (conjSrc_injective (IsCMField.complexConj E).toRingEquiv).tendsto_cofinite.eventually h1
  filter_upwards [h1, h2] with w a b
  obtain ⟨B, hB, hP⟩ := a (w.under (𝓞 F)) rfl _ (normV_under w)
  obtain ⟨B', hB', hP'⟩ := b (w.under (𝓞 F)) (by
    have e := cPl_asIdeal w
    change _ = (cPl w).asIdeal.comap _
    rw [e]
    ext x
    have e2 : RingOfIntegers.mapRingEquiv (IsCMField.complexConj E).toRingEquiv (algebraMap (𝓞 F) (𝓞 E) x) =
        algebraMap (𝓞 F) (𝓞 E) x := RingOfIntegers.ext (conj_algebraMap (x : F))
    rw [Ideal.mem_comap, Ideal.mem_comap, e2]
    rfl) _ ((normV_cPl w).trans (normV_under w))
  obtain rfl := TR.CuspSub.HasSat.unique hB hB'
  exact ⟨_, hP, hP'⟩
