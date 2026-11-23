import Mathlib
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.TensFactor
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.EigBasic
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.LineRank
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.OccursBasics
import GroundTheory.AutomorphicForms.Satake

open MeasureTheory GroundTheory.Automorphic UpperTheory.ConvolutionTheory.C

theorem UpperTheory.ConvolutionTheory.L1.sphRank :
    UpperTheory.ConvolutionTheory.L1.SphRank := by
  intro K _ _ n μ _ V hV w
  letI : MeasurableSpace (Gw n w) := borel _
  haveI : BorelSpace (Gw n w) := ⟨rfl⟩
  obtain ⟨⟨σ, hσ⟩, -, -⟩ := UpperTheory.ConvolutionTheory.C.occursBasics K n μ V w Measure.haar hV
  have hmem : ∀ x : σ.V, (∀ g ∈ GLnLocal.integralGL (w.adicCompletion K) n,
      σ.ρ g x = (1 : Gw n w → ℂ) g • x) → x ∈ fixedVectors σ.ρ (GLnLocal.integralGL (w.adicCompletion K) n) := by
    intro x hx
    exact fun g hg => by simpa using hx g hg
  refine UpperTheory.ConvolutionTheory.L1.lineRank K n μ V hV w σ hσ _ 1
    ⟨GLnLocal.isCompact_integralGL _ n, GLnLocal.isOpen_integralGL _ n⟩
    ⟨IsLocallyConstant.const 1, fun _ _ => by simp, fun _ _ _ _ => by simp⟩ ?_
  by_cases h : fixedVectors σ.ρ (GLnLocal.integralGL (w.adicCompletion K) n) = ⊥
  · refine ⟨0, fun x hx => ⟨0, ?_⟩⟩
    have hx' := hmem x hx
    rw [h] at hx'
    simpa using hx'
  · haveI := σ.irred
    obtain ⟨e, -, hall⟩ := finrank_eq_one_iff'.1 (Spherical.finrank_fixedVectors_eq_one σ.smooth h)
    refine ⟨e, fun x hx => ?_⟩
    obtain ⟨c, hc⟩ := hall ⟨x, hmem x hx⟩
    exact ⟨c, by simpa using (congrArg Subtype.val hc).symm⟩
