import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IntegralCompression.LAbove
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IntegralCompression.ContinuousEntryCharacters.CoefEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IntegralCompression.ContinuousEntryCharacters.CoefIdem
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IntegralCompression.ContinuousEntryCharacters.CoefFix
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IntegralCompression.ContinuousEntryCharacters.CoefInj
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IntegralCompression.ContinuousEntryCharacters.LongWeylSwapsBlockDiagonal

open MeasureTheory NumberField Filter Topology Matrix
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Automorphic.ArchWhittakerC UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA
open scoped ComplexConjugate Classical InnerProductSpace

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA.ext4 :
    ∀ (μ : Measure U4), Haar4 μ → μ.IsOpenPosMeasure → ∀ n q n' q', ∃ e, Ext μ e n q n' q' 1 ∧ Ext μ e n' q' n q w4 := by
  intro μ hμ hpos n q n' q'
  obtain ⟨ψ, hψ⟩ := coefEx n q n' q'
  obtain ⟨hc, -, hidem, hfix⟩ := coefIdem μ ψ n q n' q' hμ hpos hψ
  have hF := coefFix μ ψ n q n' q' hμ hpos hψ
  have hI := coefInj μ ψ n q n' q' hμ hpos hψ
  obtain ⟨-, -, -, -, -, hww, hwb, -⟩ := u4
  have hsc : ∀ (c : ℂ) (x : U4), RFix μ (eOf μ ψ) (fun k => c * ψ (x * k)) := by
    intro c x g
    have h := hfix (x * g)
    show ∫ k, eOf μ ψ k * (c * ψ (x * (g * k))) ∂μ = c * ψ (x * g)
    rw [← h, ← integral_const_mul]
    congr 1
    funext k
    rw [mul_assoc x g k]
    ring
  have hcc : ∀ (c : ℂ) (x : U4), Continuous (fun k => c * ψ (x * k)) := fun c x =>
    continuous_const.mul (hc.comp (continuous_const.mul continuous_id))
  refine ⟨eOf μ ψ, ⟨hidem, ?_, ?_, ?_⟩, ⟨hidem, ?_, ?_, ?_⟩⟩
  · intro Φ hΦ hR g
    simpa only [mul_one] using hF Φ hΦ hR g
  · intro Φ hΦ hR h1 h2 h0
    exact hI Φ hΦ hR h1 h2 (by simpa only [mul_one] using h0)
  · refine ⟨_, hcc (((KT.normSqInt n q : ℝ) : ℂ)⁻¹ * ((KT.normSqInt n' q' : ℝ) : ℂ)⁻¹) 1, hsc _ 1, ?_⟩
    intro a b
    simp only [mul_one, one_mul, hψ.res, T, map_mul, map_inv₀, Complex.conj_ofReal, Complex.conj_conj]
    ring
  · intro Φ hΦ hR g
    obtain ⟨h1, h2⟩ := hF Φ hΦ hR (g * w4)
    refine ⟨?_, ?_⟩
    · rw [← h2]
      congr 1
      funext m
      rw [mul_assoc g w4, hwb, mul_assoc g]
    · rw [← h1]
      congr 1
      funext m
      rw [mul_assoc g w4, hwb, mul_assoc g]
  · intro Φ hΦ hR h1 h2 h0
    have key : (fun k => Φ (w4 * k)) = 0 := by
      refine hI _ (hΦ.comp (continuous_const.mul continuous_id)) ?_ ?_ ?_ ?_
      · intro g
        have h := hR (w4 * g)
        simpa only [mul_assoc] using h
      · intro N Q hN l k
        have h := h2 N Q hN l (w4 * k)
        simpa only [← mul_assoc w4, hwb, ← mul_assoc (bd _ _) w4] using h
      · intro N Q hN l k
        have h := h1 N Q hN l (w4 * k)
        simpa only [← mul_assoc w4, hwb, ← mul_assoc (bd _ _) w4] using h
      · intro a b
        show Φ (w4 * bd a b) = 0
        rw [hwb]
        exact h0 b a
    funext k
    have h := congrFun key (w4 * k)
    simpa only [← mul_assoc, hww, one_mul, Pi.zero_apply] using h
  · refine ⟨_, hcc (((KT.normSqInt n q : ℝ) : ℂ)⁻¹ * ((KT.normSqInt n' q' : ℝ) : ℂ)⁻¹) w4, hsc _ w4, ?_⟩
    intro a b
    have e : w4 * (bd a b * w4) = bd b a := by
      rw [← mul_assoc, hwb, mul_assoc, hww, mul_one]
    simp only [e, hψ.res, T, map_mul, map_inv₀, Complex.conj_ofReal, Complex.conj_conj]
    ring
