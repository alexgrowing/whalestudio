import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsIsFundU
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.KerBF
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.JacobiToBesselUnfoldedIntegrandIntegrableStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierJacobiIntegralOverNUnfoldStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PairedFlatMapFamilyContinuousInvariantIntegralStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf GlobalTheory.Unf.FB

namespace GlobalTheory.Unf.FB

theorem per_lift_eq_integral_unfF : ∀ (D : D7), Descent D → ∀ (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (J : JacLev D (σ + 1)) (B : BesLev D σ) (s : StepFB ψ J B), ∀ (vL : VolM D B.L.rank J.W₀.rank) (Y : GA D J.W₀ → WO J.W₀ B.L → ℂ) (G : GA D B.V → ℂ) (Φ : WO J.W B.V → ℂ), IsQuasiFam ψ J.W₀ B.L Y → RapidDec B.V G → IsThetaFunO ψ J.W B.V Φ → ∀ 𝓑 : Set (GA D B.V), IsFundamentalDomain (GQ B.V ⊓ besGrp B.d B.o : Subgroup (GA D B.V)) 𝓑 s.vW.μ → IntegrableOn (unfF s vL Y G Φ) 𝓑 s.vW.μ ∧ J.per ψ B.ζ Y (s.lift G Φ) = ∫ h in 𝓑, unfF s vL Y G Φ h ∂s.vW.μ := by
  intro D hD ψ σ J B s vL Y G Φ hY hG hΦ 𝓑 h𝓑
  have := s.vW.haar
  have := J.v0.haar
  have hI := GlobalTheory.T.jacobiToBessel_unfoldedIntegrand_integrable D hD ψ σ J B s vL Y G Φ hY hG hΦ 𝓑 h𝓑
  have hin := GlobalTheory.T.fourierJacobi_integral_over_N_unfold D hD ψ σ J B s vL Y G Φ hY hG hΦ 𝓑 h𝓑
  have hc := (GlobalTheory.T.pairedFlatMap_family_continuous_invariant_integral D hD ψ σ J B s vL Y Φ hY hΦ).2.2
  have hU : ∀ h, unfF s vL Y G Φ h = ∫ h₀ in J.v0.𝓕, G h * tFlat s vL (Y h₀) (s.om (J.d.emb0 h₀, h) Φ) ∂J.v0.μ := by
    intro h
    rw [unfF, hc h, integral_const_mul]
  constructor
  · have := hI.integral_prod_right
    refine this.congr ?_
    exact Filter.Eventually.of_forall fun h => (hU h).symm
  · calc J.per ψ B.ζ Y (s.lift G Φ)
        = ∫ h₀ in J.v0.𝓕, ∫ h in 𝓑, G h * tFlat s vL (Y h₀) (s.om (J.d.emb0 h₀, h) Φ) ∂s.vW.μ ∂J.v0.μ := by
          unfold JacLev.per fjSrcKer
          congr 1
          funext h₀
          exact hin h₀
      _ = ∫ h in 𝓑, ∫ h₀ in J.v0.𝓕, G h * tFlat s vL (Y h₀) (s.om (J.d.emb0 h₀, h) Φ) ∂J.v0.μ ∂s.vW.μ :=
          integral_integral_swap hI
      _ = ∫ h in 𝓑, unfF s vL Y G Φ h ∂s.vW.μ := by
          congr 1
          funext h
          exact (hU h).symm

end GlobalTheory.Unf.FB

end
