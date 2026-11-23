import Mathlib
import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalIdeles.RamDefs
import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalIdeles.QuadLiftUnr
import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalIdeles.NormRam

open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.L2.Host Formalism.ConjugateSelfDual UpperTheory.V.Published UpperTheory.CBC

private theorem normV_two_le {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) : 2 ≤ normV v := by
  have e : normV v = Ideal.absNorm v.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
    rfl
  rw [e]
  have a := Ideal.absNorm_eq_zero_iff.not.2 v.ne_bot
  have b := Ideal.absNorm_eq_one_iff.not.2 v.isPrime.ne_top
  omega

theorem UpperTheory.ConvolutionTheory.Sph.quadLiftOf :
    UpperTheory.ConvolutionTheory.Sph.RamSph → GlobalTheory.GalCut.QuadLift := by
  intro hR K M _ _ _ _ _ _ _ h2 a ha π hw
  obtain ⟨P, hP⟩ := UpperTheory.ConvolutionTheory.Sph.quadLiftUnr K M h2 a ha π hw
  have hp : (Module.finrank K M).Prime := h2 ▸ Nat.prime_two
  haveI : Algebra.IsQuadraticExtension K M := { finrank_eq_two' := h2 }
  haveI : IsGalois K M := Algebra.IsQuadraticExtension.isGalois K M
  refine ⟨P, ⟨fun w f B hf hB => ?_, hP.inf, hP.loc⟩⟩
  by_cases hu : Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal
  · exact hP.sat w f B hu hf hB
  · have h1 := (UpperTheory.ConvolutionTheory.Sph.normRam K M hp w hu).1
    have hf1 : f = 1 := by
      have h3 : normV (w.under (𝓞 K)) ^ 1 = normV (w.under (𝓞 K)) ^ f := by rw [pow_one, ← hf, h1]
      exact (Nat.pow_right_injective (normV_two_le _) h3).symm
    subst hf1
    have e : B.map (· ^ 1) = B := by simp
    rw [e]
    exact hR K M hp a ha π P hP.weak w hu B hB
