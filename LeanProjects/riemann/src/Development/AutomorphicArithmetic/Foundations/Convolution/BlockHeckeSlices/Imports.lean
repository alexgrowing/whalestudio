import Development.AutomorphicArithmetic.Foundations.Convolution.ASmooth
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.DatDatum
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.KillCore
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.FunKill
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.DatDatum

open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.BW PositivityTheory.Rg.Tf.Core

theorem UpperTheory.ConvolutionTheory.kill :
    UpperTheory.ConvolutionTheory.Kill := by
  intro K _ _ _ n hn μ _ 𝔞 η hη
  obtain ⟨ρ, Cb, hCb, hcore⟩ := killCore hn 𝔞 η hη
  obtain ⟨D, hD, hlen, hk⟩ := funKill K 𝔞.S n ρ Cb hCb
  choose b hb1 hb2 using fun d : D => datDatum K 𝔞.S n d.1 (hlen d.1 d.2)
  refine ⟨D, hD.fintype, b, hb1, fun ev hev χ hχ hχ0 _ F G hF hFb hG => ?_⟩
  refine hcore ev hev 0 (1 - Pc μ) (fun R _ => by rw [ContinuousLinearMap.comp_zero, ContinuousLinearMap.zero_comp]) ?_
    (ContinuousLinearMap.zero_comp _) χ hχ hχ0 F G hF hG fun y φ w _ hw hφ hs hkw hsw hsum =>
      hk φ w F G hφ hs hw.umg hkw hsw hF.2 (fun d hd => hb2 ⟨d, hd⟩ F hF.2 (hFb ⟨d, hd⟩)) hG hsum
  exact (Submodule.isIdempotentElem_starProjection _).mul_one_sub_self
