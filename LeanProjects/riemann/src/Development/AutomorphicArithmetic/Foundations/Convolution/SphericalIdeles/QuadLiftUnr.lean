import Mathlib
import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalIdeles.RamDefs
import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalIdeles.LiftUnr
import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalIdeles.NormRam
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CuspidalTwistRamifiedCharNeSelfStatement

open NumberField IsDedekindDomain

theorem UpperTheory.ConvolutionTheory.Sph.quadLiftUnr :
    UpperTheory.ConvolutionTheory.Sph.QuadLiftUnr := by
  intro K M _ _ _ _ _ _ _ h2 a ha π ⟨w, hram, B, hB⟩
  haveI : Algebra.IsQuadraticExtension K M := ⟨h2⟩
  haveI : IsGalois K M := inferInstance
  have hp : (Module.finrank K M).Prime := h2 ▸ Nat.prime_two
  exact UpperTheory.ConvolutionTheory.Sph.liftUnr K M hp a ha π fun η hη =>
    GlobalTheory.T.cuspidal_twist_ramified_char_ne_self K a ha _ η (w.under (𝓞 K)) B hB ((UpperTheory.ConvolutionTheory.Sph.normRam K M hp w hram).2.2 η hη)
