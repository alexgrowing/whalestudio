import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsIsFundU
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.KerBF
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnfoldedFunctionEqBesselPeriodIntegrandStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselGroupSemidirectProductRationalStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PairedFlatMapFamilyContinuousInvariantIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatThetaMapsConvergeThetaFunctionsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierJacobiHandOffAutomorphicStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatThetaMapsPreserveThetaFunctionsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousIntegralCompactAutomorphicQuotientParaStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentBesselCharacterLaws

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf GlobalTheory.Unf.FB

namespace GlobalTheory.Unf.FB

theorem unfF_continuous_invariant : ∀ (D : D7), Descent D → ∀ (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (J : JacLev D (σ + 1)) (B : BesLev D σ) (s : StepFB ψ J B), ∀ (vL : VolM D B.L.rank J.W₀.rank) (Y : GA D J.W₀ → WO J.W₀ B.L → ℂ) (G : GA D B.V → ℂ) (Φ : WO J.W B.V → ℂ), IsQuasiFam ψ J.W₀ B.L Y → RapidDec B.V G → IsThetaFunO ψ J.W B.V Φ → Continuous (unfF s vL Y G Φ) ∧ ∀ γ ∈ (GQ B.V ⊓ besGrp B.d B.o : Subgroup (GA D B.V)), ∀ h, unfF s vL Y G Φ (γ * h) = unfF s vL Y G Φ h := by
  intro D hD ψ σ J B s vL Y G Φ hY hG hΦ
  refine ⟨?_, ?_⟩
  · obtain ⟨hc, hi, he⟩ := GlobalTheory.T.pairedFlatMap_family_continuous_invariant_integral D hD ψ σ J B s vL Y Φ hY hΦ
    have h1 := (GlobalTheory.T.continuous_integral_compactAutomorphicQuotient_param D J.W₀ J.cpt J.v0 (GA D B.V)
      (fun h₀ h => tFlat s vL (Y h₀) (s.om (J.d.emb0 h₀, h) Φ)) hc hi).2.1
    have h2 : unfF s vL Y G Φ = fun h => G h *
        ∫ h₀ in J.v0.𝓕, tFlat s vL (Y h₀) (s.om (J.d.emb0 h₀, h) Φ) ∂J.v0.μ := by
      funext h
      rw [unfF, he h]
    rw [h2]
    exact hG.2.1.mul h1
  · intro γ hγ h
    obtain ⟨hq, hb⟩ := Subgroup.mem_inf.1 hγ
    obtain ⟨-, hone, -, -, hdec, -⟩ :=
      GlobalTheory.MixPer.charLaws D ψ s.weil.std.1 B.V B.V₀ B.A B.L σ B.d B.o B.ζ 1
    obtain ⟨n, hn, h₁, rfl⟩ := (hdec γ).1 hb
    obtain ⟨hnq, hhq⟩ := ((GlobalTheory.T.besselGroup_semidirectProduct_rational D σ B).2.2.2.2 n hn h₁).1 hq
    have hth : IsThetaFunO ψ J.W₀ B.V₀ (flatFB s (s.om (1, h) Φ)) :=
      (GlobalTheory.T.flatThetaMaps_preserve_thetaFunctions D (GlobalTheory.T.flatThetaMaps_converge_thetaFunctions D) ψ).2 σ J B s _ (s.weil.om_pres _ _ hΦ)
    have hinv := (GlobalTheory.T.fourierJacobiHandOff_automorphic D ψ σ J B s vL Y _ hY hth).1 h₁ hhq 1
    rw [mul_one] at hinv
    have e := GlobalTheory.T.unfoldedFunction_eq_besselPeriodIntegrand D hD ψ σ J B s vL Y G Φ hΦ h h₁ ⟨n, hn⟩
    refine e.trans ?_
    simp only [besFun, rTrans, unfF]
    rw [hinv, hone _ n hnq, hG.1 _ hq h, star_one, mul_one, mul_comm]

end GlobalTheory.Unf.FB
