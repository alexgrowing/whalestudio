import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.PlaceAe
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.GoodOfGoodAt
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.AeInt
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.EigenvalueSumMulThetaConstantTermEqZeroOfAnisotr
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.SelfIso
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.StrongMultOneReal
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HeckeAdjoints.SatLocFree
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.EigOfSat
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.Smooth

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2

private theorem ev_below {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {p : HeightOneSpectrum (𝓞 E) → Prop} (h : ∀ᶠ w in cofinite, p w) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, ∃ w, H.Below v w ∧ p w := by
  have ex : ∀ v : HeightOneSpectrum (𝓞 F), ∃ w : HeightOneSpectrum (𝓞 E), H.Below v w := fun v => by
    have := v.isMaximal
    obtain ⟨Q, hQ, hl⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 E) v.asIdeal
    exact ⟨⟨Q, hQ.isPrime, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩, hl.over⟩
  choose g hg using ex
  have hi : Function.Injective g := fun v v' e => HeightOneSpectrum.ext ((hg v).trans (e ▸ (hg v').symm))
  filter_upwards [hi.tendsto_cofinite.eventually h] with v hv using ⟨g v, hg v, hv⟩

open UpperTheory.ConvolutionTheory.R2.H in
theorem UpperTheory.ConvolutionTheory.R2.dih :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (D : Dat F E) (W : Weil D) (M : Meas F) (π : TR.CuspSub F 2), St.Dih W M π := by
  intro F E _ _ _ _ _ _ _ D W M π _ h0
  simp only [ThetaLiftTrivialOrbitTermsVanish, not_forall] at h0
  obtain ⟨f, hf, φ, hφ, h, hT⟩ := h0
  refine UpperTheory.V.Br.selfIso UpperTheory.V.Af.strongMultOneReal F 2 one_le_two π W.η
    (Subtype.ext (MonoidHom.ext fun a => W.η_sq a)) ?_
  have hδ : D.δ ≠ 0 := fun e => by
    have h1 : D.θ = 0 := pow_eq_zero_iff two_ne_zero |>.1 (by rw [D.sq, e, map_zero])
    exact D.b.ne_zero 1 (D.b1.trans h1)
  have hl : IsOpen {k : GL (Fin 2) (Af F) | ∀ g, f.1 (g * finGL F 2 k) = f.1 g} := by
    convert (π.cusp f hf).1.level using 1
    exact Set.ext fun k => ⟨fun a => Subtype.ext (funext a), fun a g => congrFun (congrArg Subtype.val a) g⟩
  filter_upwards [ev_below (W.quad.and (placeAe F E D)), gdAe F D.δ hδ, (aeK F).2.1 (nu F h), (aeK F).2.2 f.1 hl,
    W.unr (W.L h φ), UpperTheory.V.Af.Gk.satAE F 2 π] with v ⟨w, hw, hq, hp⟩ hg hk hfix hu ⟨B, hB⟩
  obtain ⟨h1, h2⟩ := hq v hw
  refine ⟨h1, B, hB, ?_⟩
  rcases hp v hw with hs | hi
  · rw [h2, if_pos hs.1]; simp
  · have hn : normV w ≠ normV v := fun e => by
      have h3 := hi.norm
      have h4 : 1 < normV v := by
        have := GlobalTheory.LFun.one_lt_absNorm v
        simpa [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply] using this
      rw [e] at h3
      nlinarith
    obtain ⟨α, β, rfl⟩ := Multiset.card_eq_two.1 hB.card
    have h5 := eigenvalue_sum_mul_thetaConstantTerm_eq_zero_of_anisotropic F E D W M π v hg hi.aniso f hf φ hφ h α β (UpperTheory.V.Af.Smo.eigOfSat F 2 π v _ hB f hf hfix) hk hu
    have h6 : β = -α := Units.ext (by
      have := (mul_eq_zero.1 h5).resolve_right hT
      simpa using eq_neg_of_add_eq_zero_right this)
    rw [h2, if_neg hn, h6]
    simp [Multiset.cons_swap]
    exact Multiset.pair_comm _ _
