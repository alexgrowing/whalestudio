import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.ResEmbCompat
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.Places

open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.Gal.InertialTypesAlt.resDeg :
    CardRes → ResDeg := by
  intro hcard K M _ _ _ _ _ _ hn v w hns hunr _
  classical
  have hw : (w : HeightOneSpectrum (𝓞 M)).asIdeal.LiesOver v.asIdeal := w.2
  set f := (w : HeightOneSpectrum (𝓞 M)).asIdeal.inertiaDeg (𝓞 K) with hf
  have hfconst : ∀ u : PlacesOver M v,
      (u : HeightOneSpectrum (𝓞 M)).asIdeal.inertiaDeg (𝓞 K) = f := by
    intro u
    haveI := u.2
    exact Ideal.inertiaDeg_eq_of_isGaloisGroup v.asIdeal _ _ Gal(M/K)
  have heone : ∀ u : PlacesOver M v,
      (u : HeightOneSpectrum (𝓞 M)).asIdeal.ramificationIdx (𝓞 K) = 1 := by
    intro u
    haveI := hunr u
    exact Ideal.ramificationIdx_eq_one _ _
  have hsum := GroundTheory.Global.SemiLocal.sum_ramificationIdx_mul_inertiaDeg M v
  have hdvd : f ∣ Module.finrank K M := by
    rw [← hsum]
    apply Finset.dvd_sum
    intro u _
    rw [heone u, hfconst u, one_mul]
  have hf1 : f ≠ 1 := by
    intro h1
    apply hns
    intro u
    haveI := u.2
    have hrk := GroundTheory.Global.SemiLocal.finrank_eq_ramificationIdx_mul_inertiaDeg M v
      (u : HeightOneSpectrum (𝓞 M))
    rw [heone u, hfconst u, h1, one_mul] at hrk
    have htop := Subalgebra.bot_eq_top_of_finrank_eq_one hrk
    intro y
    have hy : y ∈ (⊥ : Subalgebra (HeightOneSpectrum.adicCompletion K v)
        (HeightOneSpectrum.adicCompletion M (u : HeightOneSpectrum (𝓞 M)))) := by
      rw [htop]
      trivial
    obtain ⟨x, hx⟩ := Algebra.mem_bot.mp hy
    exact ⟨x, hx⟩
  have hfn : f = Module.finrank K M := (hn.eq_one_or_self_of_dvd f hdvd).resolve_left hf1
  have hnormK : normV v = v.asIdeal.absNorm := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
    rfl
  have hnormM : normV (w : HeightOneSpectrum (𝓞 M)) =
      (w : HeightOneSpectrum (𝓞 M)).asIdeal.absNorm := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
    rfl
  have hpow : v.asIdeal.absNorm ^ f = (w : HeightOneSpectrum (𝓞 M)).asIdeal.absNorm :=
    Ideal.absNorm_pow_inertiaDeg v.asIdeal _
  have hK := hcard K v
  have hM := hcard M (w : HeightOneSpectrum (𝓞 M))
  have hge : 2 ≤ v.asIdeal.absNorm := by
    have h0 : v.asIdeal.absNorm ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff]
      exact v.ne_bot
    have h1 : v.asIdeal.absNorm ≠ 1 := by
      rw [Ne, Ideal.absNorm_eq_one_iff]
      exact v.isPrime.ne_top
    omega
  have hcardM : Nat.card 𝓀[HeightOneSpectrum.adicCompletion M (w : HeightOneSpectrum (𝓞 M))] =
      Nat.card 𝓀[HeightOneSpectrum.adicCompletion K v] ^ Module.finrank K M := by
    rw [hM, hK, hnormM, hnormK, ← hpow, hfn]
  haveI : Finite 𝓀[HeightOneSpectrum.adicCompletion K v] :=
    Nat.finite_of_card_ne_zero (by rw [hK, hnormK]; omega)
  haveI : Finite 𝓀[HeightOneSpectrum.adicCompletion M (w : HeightOneSpectrum (𝓞 M))] :=
    Nat.finite_of_card_ne_zero (by rw [hcardM, hK, hnormK]; positivity)
  letI := Fintype.ofFinite 𝓀[HeightOneSpectrum.adicCompletion K v]
  haveI : Module.Finite 𝓀[HeightOneSpectrum.adicCompletion K v]
      𝓀[HeightOneSpectrum.adicCompletion M (w : HeightOneSpectrum (𝓞 M))] :=
    Module.Finite.of_finite
  refine ⟨?_, ?_⟩
  · have hc := Module.natCard_eq_pow_finrank (K := 𝓀[HeightOneSpectrum.adicCompletion K v])
      (V := 𝓀[HeightOneSpectrum.adicCompletion M (w : HeightOneSpectrum (𝓞 M))])
    rw [hcardM] at hc
    have h2 : 2 ≤ Nat.card 𝓀[HeightOneSpectrum.adicCompletion K v] := by
      rw [hK, hnormK]
      exact hge
    exact (Nat.pow_right_injective h2 hc).symm
  · refine ⟨FiniteField.frobeniusAlgEquivOfAlgebraic _ _, fun z => ?_⟩
    rw [FiniteField.frobeniusAlgEquivOfAlgebraic_apply, Nat.card_eq_fintype_card]
