import Mathlib
import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalIdeles.WeakStable
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResidueCardEqAbsNormStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.EqOfHasValueAtInfinite

namespace UpperTheory.ConvolutionTheory.Sph

private theorem zpow_inj_of_absNorm {F : Type} [Field F] [NumberField F] (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) {a b : ℤ}
    (h : (Ideal.absNorm v.asIdeal : ℝ) ^ a = (Ideal.absNorm v.asIdeal : ℝ) ^ b) : a = b := by
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := fun e => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 e)
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := fun e => v.isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 e)
  have h2 : 1 < Ideal.absNorm v.asIdeal := by omega
  have h3 : (1 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by exact_mod_cast h2
  exact zpow_right_injective₀ (by linarith) h3.ne' h

theorem unrNorm : UnrNorm := by
  intro F E _ _ _ _ _ v w σw l N hN hq a
  refine MonoidHom.ext fun x => ?_
  have h := hN.abs x
  rw [GlobalTheory.LGrp.nabs_eq_zpow, GlobalTheory.LGrp.nabs_eq_zpow, GlobalTheory.T.residue_card_eq_abs_norm F v, GlobalTheory.T.residue_card_eq_abs_norm E w.1, hq] at h
  have h' := zpow_inj_of_absNorm v h
  have h'' := neg_injective h'
  simp only [MonoidHom.comp_apply, GlobalTheory.SmGL.unrChar_apply, h'']

end UpperTheory.ConvolutionTheory.Sph
